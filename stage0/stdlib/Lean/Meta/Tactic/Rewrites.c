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
lean_object* l_Option_toLOption___redArg(lean_object*);
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
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t v___x_435_, lean_object* v___x_436_, lean_object* v___f_437_, uint8_t v___x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
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
v___x_490_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v___x_436_, v___f_437_, v___x_438_, v___x_438_, v___x_489_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___x_489_);
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v___f_504_, lean_object* v___x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_7247__boxed_511_; uint8_t v___x_7250__boxed_512_; lean_object* v_res_513_; 
v___x_7247__boxed_511_ = lean_unbox(v___x_502_);
v___x_7250__boxed_512_ = lean_unbox(v___x_505_);
v_res_513_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_7247__boxed_511_, v___x_503_, v___f_504_, v___x_7250__boxed_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_522_, lean_object* v_constInfo_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Lean_ConstantInfo_isUnsafe(v_constInfo_523_);
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
lean_object* v_str_557_; uint8_t v___y_559_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_str_557_ = lean_ctor_get(v_name_522_, 1);
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_568_ = lean_string_dec_eq(v_str_557_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_570_ = lean_string_dec_eq(v_str_557_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_572_ = lean_string_utf8_byte_size(v_str_557_);
v___x_573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_574_ = lean_nat_dec_le(v___x_573_, v___x_572_);
if (v___x_574_ == 0)
{
v___y_559_ = v___x_541_;
goto v___jp_558_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_sub(v___x_572_, v___x_573_);
v___x_577_ = lean_string_memcmp(v_str_557_, v___x_571_, v___x_576_, v___x_575_, v___x_573_);
lean_dec(v___x_576_);
v___y_559_ = v___x_577_;
goto v___jp_558_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
goto v___jp_537_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
goto v___jp_537_;
}
v___jp_558_:
{
if (v___y_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_561_ = lean_string_utf8_byte_size(v_str_557_);
v___x_562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
v___x_563_ = lean_nat_dec_le(v___x_562_, v___x_561_);
if (v___x_563_ == 0)
{
v___y_544_ = v_a_524_;
v___y_545_ = v_a_525_;
v___y_546_ = v_a_526_;
v___y_547_ = v_a_527_;
goto v___jp_543_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_nat_sub(v___x_561_, v___x_562_);
v___x_566_ = lean_string_memcmp(v_str_557_, v___x_560_, v___x_565_, v___x_564_, v___x_562_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
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
goto v___jp_537_;
}
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
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
lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___x_554_; 
v___x_549_ = l_Lean_ConstantInfo_type(v_constInfo_523_);
v___x_550_ = 2;
v___x_551_ = lean_box(v___x_550_);
v___x_552_ = lean_box(v___x_548_);
v___f_553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_553_, 0, v___x_551_);
lean_closure_set(v___f_553_, 1, v___x_549_);
lean_closure_set(v___f_553_, 2, v___f_542_);
lean_closure_set(v___f_553_, 3, v___x_552_);
v___x_554_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_553_, v___x_548_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___f_542_);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_name_522_);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
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
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_name_522_);
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_582_, lean_object* v_constInfo_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_582_, v_constInfo_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec_ref(v_constInfo_583_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
uint8_t v___x_592_; 
v___x_592_ = 0;
return v___x_592_;
}
else
{
lean_object* v_head_593_; lean_object* v_tail_594_; uint8_t v___x_595_; 
v_head_593_ = lean_ctor_get(v_x_591_, 0);
v_tail_594_ = lean_ctor_get(v_x_591_, 1);
v___x_595_ = l_Lean_instBEqFVarId_beq(v_a_590_, v_head_593_);
if (v___x_595_ == 0)
{
v_x_591_ = v_tail_594_;
goto _start;
}
else
{
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_597_, lean_object* v_x_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec(v_a_597_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_601_, lean_object* v_as_602_, size_t v_sz_603_, size_t v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_a_612_; uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_604_, v_sz_603_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_b_605_);
return v___x_617_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_618_ = lean_array_uget_borrowed(v_as_602_, v_i_604_);
v___x_619_ = l_Lean_Expr_fvarId_x21(v_a_618_);
v___x_620_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_619_, v_except_601_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
lean_inc(v_a_618_);
v___x_621_ = lean_infer_type(v_a_618_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_box(0);
v___x_624_ = 0;
v___x_625_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_622_, v___x_623_, v___x_624_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_698_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v_snd_627_ = lean_ctor_get(v_a_626_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_626_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_a_626_, 0);
lean_dec(v_unused_699_);
v___x_629_ = v_a_626_;
v_isShared_630_ = v_isSharedCheck_698_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_dec(v_a_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_698_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_696_; 
v_snd_631_ = lean_ctor_get(v_snd_627_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_snd_627_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_snd_627_, 0);
lean_dec(v_unused_697_);
v___x_633_ = v_snd_627_;
v_isShared_634_ = v_isSharedCheck_696_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_dec(v_snd_627_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_696_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_whnfR(v_snd_631_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v_fst_638_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Expr_getAppFnArgs(v_a_636_);
v_fst_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_fst_638_);
if (lean_obj_tag(v_fst_638_) == 1)
{
lean_object* v_pre_639_; 
v_pre_639_ = lean_ctor_get(v_fst_638_, 0);
if (lean_obj_tag(v_pre_639_) == 0)
{
lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_686_; 
v_snd_640_ = lean_ctor_get(v___x_637_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_687_);
v___x_642_ = v___x_637_;
v_isShared_643_ = v_isSharedCheck_686_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_dec(v___x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_686_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_str_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_str_644_ = lean_ctor_get(v_fst_638_, 1);
lean_inc_ref(v_str_644_);
lean_dec_ref_known(v_fst_638_, 2);
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_646_ = lean_string_dec_eq(v_str_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_648_ = lean_string_dec_eq(v_str_644_, v___x_647_);
lean_dec_ref(v_str_644_);
if (v___x_648_ == 0)
{
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_array_get_size(v_snd_640_);
lean_dec(v_snd_640_);
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_nat_dec_eq(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_del_object(v___x_642_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_box(v___x_620_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_650_);
lean_ctor_set(v___x_642_, 0, v___x_652_);
v___x_654_ = v___x_642_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_650_);
v___x_654_ = v_reuseFailAlloc_666_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
lean_inc(v_a_618_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_654_);
lean_ctor_set(v___x_633_, 0, v_a_618_);
v___x_656_ = v___x_633_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_618_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_665_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = lean_array_push(v_b_605_, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_box(v___x_616_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_658_);
lean_ctor_set(v___x_629_, 0, v___x_659_);
v___x_661_ = v___x_629_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_658_);
v___x_661_ = v_reuseFailAlloc_664_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_inc(v_a_618_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_a_618_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_array_push(v___x_657_, v___x_662_);
v_a_612_ = v___x_663_;
goto v___jp_611_;
}
}
}
}
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
lean_dec_ref(v_str_644_);
v___x_667_ = lean_array_get_size(v_snd_640_);
lean_dec(v_snd_640_);
v___x_668_ = lean_unsigned_to_nat(3u);
v___x_669_ = lean_nat_dec_eq(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_del_object(v___x_642_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_670_ = lean_unsigned_to_nat(2u);
v___x_671_ = lean_box(v___x_620_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_670_);
lean_ctor_set(v___x_642_, 0, v___x_671_);
v___x_673_ = v___x_642_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_670_);
v___x_673_ = v_reuseFailAlloc_685_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
lean_inc(v_a_618_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_673_);
lean_ctor_set(v___x_633_, 0, v_a_618_);
v___x_675_ = v___x_633_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_618_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_684_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_676_ = lean_array_push(v_b_605_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_box(v___x_616_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_677_);
lean_ctor_set(v___x_629_, 0, v___x_678_);
v___x_680_ = v___x_629_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_677_);
v___x_680_ = v_reuseFailAlloc_683_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc(v_a_618_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_a_618_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_array_push(v___x_676_, v___x_681_);
v_a_612_ = v___x_682_;
goto v___jp_611_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_638_, 2);
lean_dec_ref(v___x_637_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
}
else
{
lean_dec(v_fst_638_);
lean_dec_ref(v___x_637_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
lean_dec_ref(v_b_605_);
v_a_688_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_635_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_635_);
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
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_b_605_);
v_a_700_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_625_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_625_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_b_605_);
v_a_708_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_621_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_621_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
v_a_612_ = v_b_605_;
goto v___jp_611_;
}
}
v___jp_611_:
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_604_, v___x_613_);
v_i_604_ = v___x_614_;
v_b_605_ = v_a_612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_716_, lean_object* v_as_717_, lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
size_t v_sz_boxed_726_; size_t v_i_boxed_727_; lean_object* v_res_728_; 
v_sz_boxed_726_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_727_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_716_, v_as_717_, v_sz_boxed_726_, v_i_boxed_727_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_as_717_);
lean_dec(v_except_716_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_b_732_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_b_732_);
return v___x_735_;
}
else
{
lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_754_; 
v_snd_736_ = lean_ctor_get(v_b_732_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_b_732_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_b_732_, 0);
lean_dec(v_unused_755_);
v___x_738_ = v_b_732_;
v_isShared_739_ = v_isSharedCheck_754_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_dec(v_b_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_754_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v_a_742_; lean_object* v_a_749_; 
v___x_740_ = lean_box(0);
v_a_749_ = lean_array_uget_borrowed(v_as_729_, v_i_731_);
if (lean_obj_tag(v_a_749_) == 0)
{
v_a_742_ = v_snd_736_;
goto v___jp_741_;
}
else
{
lean_object* v_val_750_; uint8_t v___x_751_; 
v_val_750_ = lean_ctor_get(v_a_749_, 0);
v___x_751_ = l_Lean_LocalDecl_isImplementationDetail(v_val_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_inc(v_val_750_);
v___x_752_ = l_Lean_LocalDecl_toExpr(v_val_750_);
v___x_753_ = lean_array_push(v_snd_736_, v___x_752_);
v_a_742_ = v___x_753_;
goto v___jp_741_;
}
else
{
v_a_742_ = v_snd_736_;
goto v___jp_741_;
}
}
v___jp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v_a_742_);
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_a_742_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
size_t v___x_745_; size_t v___x_746_; 
v___x_745_ = ((size_t)1ULL);
v___x_746_ = lean_usize_add(v_i_731_, v___x_745_);
v_i_731_ = v___x_746_;
v_b_732_ = v___x_744_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_762_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_756_, v_sz_boxed_761_, v_i_boxed_762_, v_b_759_);
lean_dec_ref(v_as_756_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_764_, size_t v_sz_765_, size_t v_i_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_lt(v_i_766_, v_sz_765_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_b_767_);
return v___x_774_;
}
else
{
lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_793_; 
v_snd_775_ = lean_ctor_get(v_b_767_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_b_767_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_b_767_, 0);
lean_dec(v_unused_794_);
v___x_777_ = v_b_767_;
v_isShared_778_ = v_isSharedCheck_793_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_dec(v_b_767_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_793_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v_a_781_; lean_object* v_a_788_; 
v___x_779_ = lean_box(0);
v_a_788_ = lean_array_uget_borrowed(v_as_764_, v_i_766_);
if (lean_obj_tag(v_a_788_) == 0)
{
v_a_781_ = v_snd_775_;
goto v___jp_780_;
}
else
{
lean_object* v_val_789_; uint8_t v___x_790_; 
v_val_789_ = lean_ctor_get(v_a_788_, 0);
v___x_790_ = l_Lean_LocalDecl_isImplementationDetail(v_val_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc(v_val_789_);
v___x_791_ = l_Lean_LocalDecl_toExpr(v_val_789_);
v___x_792_ = lean_array_push(v_snd_775_, v___x_791_);
v_a_781_ = v___x_792_;
goto v___jp_780_;
}
else
{
v_a_781_ = v_snd_775_;
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_a_781_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_783_ = v___x_777_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_781_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_766_, v___x_784_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_764_, v_sz_765_, v___x_785_, v___x_783_);
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_795_, lean_object* v_sz_796_, lean_object* v_i_797_, lean_object* v_b_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_796_);
lean_dec(v_sz_796_);
v_i_boxed_805_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_795_, v_sz_boxed_804_, v_i_boxed_805_, v_b_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v_as_795_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_807_, lean_object* v_n_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
if (lean_obj_tag(v_n_808_) == 0)
{
lean_object* v_cs_815_; lean_object* v___x_816_; lean_object* v___x_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v_cs_815_ = lean_ctor_get(v_n_808_, 0);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_b_809_);
v_sz_818_ = lean_array_size(v_cs_815_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_807_, v_cs_815_, v_sz_818_, v___x_819_, v___x_817_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_835_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_835_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; 
v_fst_825_ = lean_ctor_get(v_a_821_, 0);
if (lean_obj_tag(v_fst_825_) == 0)
{
lean_object* v_snd_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v_snd_826_ = lean_ctor_get(v_a_821_, 1);
lean_inc(v_snd_826_);
lean_dec(v_a_821_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v_snd_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; 
lean_inc_ref(v_fst_825_);
lean_dec(v_a_821_);
v_val_831_ = lean_ctor_get(v_fst_825_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v_fst_825_, 1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_val_831_);
v___x_833_ = v___x_823_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_831_);
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
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_820_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_820_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_vs_844_; lean_object* v___x_845_; lean_object* v___x_846_; size_t v_sz_847_; size_t v___x_848_; lean_object* v___x_849_; 
v_vs_844_ = lean_ctor_get(v_n_808_, 0);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_b_809_);
v_sz_847_ = lean_array_size(v_vs_844_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_844_, v_sz_847_, v___x_848_, v___x_846_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_864_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_864_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_fst_854_; 
v_fst_854_ = lean_ctor_get(v_a_850_, 0);
if (lean_obj_tag(v_fst_854_) == 0)
{
lean_object* v_snd_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v_snd_855_ = lean_ctor_get(v_a_850_, 1);
lean_inc(v_snd_855_);
lean_dec(v_a_850_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_snd_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_object* v_val_860_; lean_object* v___x_862_; 
lean_inc_ref(v_fst_854_);
lean_dec(v_a_850_);
v_val_860_ = lean_ctor_get(v_fst_854_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_fst_854_, 1);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_val_860_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_val_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_849_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_849_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_873_, lean_object* v_as_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_lt(v_i_876_, v_sz_875_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_b_877_);
return v___x_884_;
}
else
{
lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_919_; 
v_snd_885_ = lean_ctor_get(v_b_877_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_b_877_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_b_877_, 0);
lean_dec(v_unused_920_);
v___x_887_ = v_b_877_;
v_isShared_888_ = v_isSharedCheck_919_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_dec(v_b_877_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_919_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_array_uget_borrowed(v_as_874_, v_i_876_);
lean_inc(v_snd_885_);
v___x_890_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_873_, v_a_889_, v_snd_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_910_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_910_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_a_891_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_895_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_885_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_897_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_del_object(v___x_893_);
lean_dec(v_snd_885_);
v_a_902_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v_a_891_, 1);
v___x_903_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_a_902_);
lean_ctor_set(v___x_887_, 0, v___x_903_);
v___x_905_ = v___x_887_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_902_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
size_t v___x_906_; size_t v___x_907_; 
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_876_, v___x_906_);
v_i_876_ = v___x_907_;
v_b_877_ = v___x_905_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_del_object(v___x_887_);
lean_dec(v_snd_885_);
v_a_911_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_890_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_890_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_921_, lean_object* v_as_922_, lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_sz_boxed_931_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_932_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_921_, v_as_922_, v_sz_boxed_931_, v_i_boxed_932_, v_b_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v_as_922_);
lean_dec_ref(v_init_921_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_934_, lean_object* v_n_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_934_, v_n_935_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_n_935_);
lean_dec_ref(v_init_934_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_943_, size_t v_sz_944_, size_t v_i_945_, lean_object* v_b_946_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_946_);
return v___x_949_;
}
else
{
lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_968_; 
v_snd_950_ = lean_ctor_get(v_b_946_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_b_946_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_b_946_, 0);
lean_dec(v_unused_969_);
v___x_952_ = v_b_946_;
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_dec(v_b_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v_a_956_; lean_object* v_a_963_; 
v___x_954_ = lean_box(0);
v_a_963_ = lean_array_uget_borrowed(v_as_943_, v_i_945_);
if (lean_obj_tag(v_a_963_) == 0)
{
v_a_956_ = v_snd_950_;
goto v___jp_955_;
}
else
{
lean_object* v_val_964_; uint8_t v___x_965_; 
v_val_964_ = lean_ctor_get(v_a_963_, 0);
v___x_965_ = l_Lean_LocalDecl_isImplementationDetail(v_val_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_inc(v_val_964_);
v___x_966_ = l_Lean_LocalDecl_toExpr(v_val_964_);
v___x_967_ = lean_array_push(v_snd_950_, v___x_966_);
v_a_956_ = v___x_967_;
goto v___jp_955_;
}
else
{
v_a_956_ = v_snd_950_;
goto v___jp_955_;
}
}
v___jp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_a_956_);
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_956_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
size_t v___x_959_; size_t v___x_960_; 
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_add(v_i_945_, v___x_959_);
v_i_945_ = v___x_960_;
v_b_946_ = v___x_958_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_976_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_970_, v_sz_boxed_975_, v_i_boxed_976_, v_b_973_);
lean_dec_ref(v_as_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_981_);
return v___x_988_;
}
else
{
lean_object* v_snd_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1007_; 
v_snd_989_ = lean_ctor_get(v_b_981_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_b_981_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v_b_981_, 0);
lean_dec(v_unused_1008_);
v___x_991_ = v_b_981_;
v_isShared_992_ = v_isSharedCheck_1007_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snd_989_);
lean_dec(v_b_981_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1007_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_a_995_; lean_object* v_a_1002_; 
v___x_993_ = lean_box(0);
v_a_1002_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
if (lean_obj_tag(v_a_1002_) == 0)
{
v_a_995_ = v_snd_989_;
goto v___jp_994_;
}
else
{
lean_object* v_val_1003_; uint8_t v___x_1004_; 
v_val_1003_ = lean_ctor_get(v_a_1002_, 0);
v___x_1004_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc(v_val_1003_);
v___x_1005_ = l_Lean_LocalDecl_toExpr(v_val_1003_);
v___x_1006_ = lean_array_push(v_snd_989_, v___x_1005_);
v_a_995_ = v___x_1006_;
goto v___jp_994_;
}
else
{
v_a_995_ = v_snd_989_;
goto v___jp_994_;
}
}
v___jp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_a_995_);
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_997_ = v___x_991_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_995_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_980_, v___x_998_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_978_, v_sz_979_, v___x_999_, v___x_997_);
return v___x_1000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1009_, lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
size_t v_sz_boxed_1018_; size_t v_i_boxed_1019_; lean_object* v_res_1020_; 
v_sz_boxed_1018_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1019_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_1009_, v_sz_boxed_1018_, v_i_boxed_1019_, v_b_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_as_1009_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1021_, lean_object* v_init_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_root_1028_; lean_object* v_tail_1029_; lean_object* v___x_1030_; 
v_root_1028_ = lean_ctor_get(v_t_1021_, 0);
v_tail_1029_ = lean_ctor_get(v_t_1021_, 1);
lean_inc_ref(v_init_1022_);
v___x_1030_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1022_, v_root_1028_, v_init_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec_ref(v_init_1022_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1067_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1067_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1067_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
if (lean_obj_tag(v_a_1031_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_a_1031_, 1);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_a_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; size_t v_sz_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
lean_del_object(v___x_1033_);
v_a_1039_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v_a_1031_, 1);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_1039_);
v_sz_1042_ = lean_array_size(v_tail_1029_);
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1029_, v_sz_1042_, v___x_1043_, v___x_1041_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1058_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_fst_1049_; 
v_fst_1049_ = lean_ctor_get(v_a_1045_, 0);
if (lean_obj_tag(v_fst_1049_) == 0)
{
lean_object* v_snd_1050_; lean_object* v___x_1052_; 
v_snd_1050_ = lean_ctor_get(v_a_1045_, 1);
lean_inc(v_snd_1050_);
lean_dec(v_a_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_snd_1050_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_snd_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1056_; 
lean_inc_ref(v_fst_1049_);
lean_dec(v_a_1045_);
v_val_1054_ = lean_ctor_get(v_fst_1049_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_fst_1049_, 1);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_val_1054_);
v___x_1056_ = v___x_1047_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_val_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_a_1059_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1044_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1044_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1030_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1030_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1076_, lean_object* v_init_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1076_, v_init_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_t_1076_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_lctx_1091_; lean_object* v_decls_1092_; lean_object* v_hs_1093_; lean_object* v___x_1094_; 
v_lctx_1091_ = lean_ctor_get(v___y_1086_, 2);
v_decls_1092_ = lean_ctor_get(v_lctx_1091_, 1);
v_hs_1093_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1094_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1092_, v_hs_1093_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1112_ = lean_array_size(v_a_1110_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1103_, v_a_1110_, v_sz_1112_, v___x_1113_, v___x_1111_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1110_);
return v___x_1114_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1109_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1109_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1130_, size_t v_sz_1131_, size_t v_i_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1130_, v_sz_1131_, v_i_1132_, v_b_1133_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1140_, lean_object* v_sz_1141_, lean_object* v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1140_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_as_1140_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1152_, size_t v_sz_1153_, size_t v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1152_, v_sz_1153_, v_i_1154_, v_b_1155_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1162_, lean_object* v_sz_1163_, lean_object* v_i_1164_, lean_object* v_b_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1163_);
lean_dec(v_sz_1163_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1162_, v_sz_boxed_1171_, v_i_boxed_1172_, v_b_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v_as_1162_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1204_, v___x_1205_, v___x_1206_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_st_mk_ref(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_unsigned_to_nat(6500u);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_snd_1223_; uint8_t v___x_1224_; 
v_snd_1223_ = lean_ctor_get(v_x_1222_, 1);
v___x_1224_ = lean_unbox(v_snd_1223_);
if (v___x_1224_ == 0)
{
lean_object* v_fst_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1237_; 
v_fst_1225_ = lean_ctor_get(v_x_1222_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_x_1222_, 1);
lean_dec(v_unused_1238_);
v___x_1227_ = v_x_1222_;
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_fst_1225_);
lean_dec(v_x_1222_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1229_ = 0;
v___x_1230_ = lean_unsigned_to_nat(2u);
v___x_1231_ = lean_nat_mul(v___x_1230_, v_x_1221_);
lean_dec(v_x_1221_);
v___x_1232_ = lean_box(v___x_1229_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1231_);
lean_ctor_set(v___x_1227_, 0, v___x_1232_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1231_);
v___x_1234_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_fst_1225_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
}
}
else
{
lean_object* v_fst_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1249_; 
v_fst_1239_ = lean_ctor_get(v_x_1222_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_x_1222_, 1);
lean_dec(v_unused_1250_);
v___x_1241_ = v_x_1222_;
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_fst_1239_);
lean_dec(v_x_1222_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1243_ = 1;
v___x_1244_ = lean_box(v___x_1243_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_x_1221_);
lean_ctor_set(v___x_1241_, 0, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_x_1221_);
v___x_1246_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_fst_1239_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1252_, lean_object* v_ty_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1259_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1260_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1261_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1262_ = lean_unsigned_to_nat(6500u);
v___x_1263_ = lean_box(0);
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1265_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1252_, v___x_1259_, v___x_1260_, v___x_1261_, v___x_1262_, v___x_1263_, v___x_1264_, v_ty_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1266_, lean_object* v_ty_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1266_, v_ty_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1274_, v_x_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1281_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1281_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1298_, lean_object* v_x_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1298_, v_x_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1306_, lean_object* v_mctx_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1307_, v_x_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_mctx_1316_, lean_object* v_x_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1315_, v_mctx_1316_, v_x_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_saveState___redArg(v___y_1326_, v___y_1328_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_r_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
v_r_1332_ = lean_apply_5(v_x_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, lean_box(0));
if (lean_obj_tag(v_r_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v_r_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v_r_1332_, 1);
v___x_1334_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1331_, v___y_1326_, v___y_1328_);
lean_dec(v_a_1331_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1342_);
v___x_1336_ = v___x_1334_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v___x_1334_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_a_1333_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1333_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_a_1333_);
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1334_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v_r_1332_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v_r_1332_, 1);
v___x_1352_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1331_, v___y_1326_, v___y_1328_);
lean_dec(v_a_1331_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1360_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 1);
lean_ctor_set(v___x_1354_, 0, v_a_1351_);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1351_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1351_);
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_x_1324_);
v_a_1369_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1330_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1330_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1392_, v_x_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1400_; uint64_t v___x_1401_; 
v___x_1400_ = 2;
v___x_1401_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1402_, uint8_t v___x_1403_, lean_object* v___x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_mkFreshExprMVar(v___x_1402_, v___x_1403_, v___x_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; uint8_t v_foApprox_1413_; uint8_t v_ctxApprox_1414_; uint8_t v_quasiPatternApprox_1415_; uint8_t v_constApprox_1416_; uint8_t v_isDefEqStuckEx_1417_; uint8_t v_unificationHints_1418_; uint8_t v_proofIrrelevance_1419_; uint8_t v_assignSyntheticOpaque_1420_; uint8_t v_offsetCnstrs_1421_; uint8_t v_etaStruct_1422_; uint8_t v_univApprox_1423_; uint8_t v_iota_1424_; uint8_t v_beta_1425_; uint8_t v_proj_1426_; uint8_t v_zeta_1427_; uint8_t v_zetaDelta_1428_; uint8_t v_zetaUnused_1429_; uint8_t v_zetaHave_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1489_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = l_Lean_Meta_Context_config(v___y_1405_);
v_foApprox_1413_ = lean_ctor_get_uint8(v___x_1412_, 0);
v_ctxApprox_1414_ = lean_ctor_get_uint8(v___x_1412_, 1);
v_quasiPatternApprox_1415_ = lean_ctor_get_uint8(v___x_1412_, 2);
v_constApprox_1416_ = lean_ctor_get_uint8(v___x_1412_, 3);
v_isDefEqStuckEx_1417_ = lean_ctor_get_uint8(v___x_1412_, 4);
v_unificationHints_1418_ = lean_ctor_get_uint8(v___x_1412_, 5);
v_proofIrrelevance_1419_ = lean_ctor_get_uint8(v___x_1412_, 6);
v_assignSyntheticOpaque_1420_ = lean_ctor_get_uint8(v___x_1412_, 7);
v_offsetCnstrs_1421_ = lean_ctor_get_uint8(v___x_1412_, 8);
v_etaStruct_1422_ = lean_ctor_get_uint8(v___x_1412_, 10);
v_univApprox_1423_ = lean_ctor_get_uint8(v___x_1412_, 11);
v_iota_1424_ = lean_ctor_get_uint8(v___x_1412_, 12);
v_beta_1425_ = lean_ctor_get_uint8(v___x_1412_, 13);
v_proj_1426_ = lean_ctor_get_uint8(v___x_1412_, 14);
v_zeta_1427_ = lean_ctor_get_uint8(v___x_1412_, 15);
v_zetaDelta_1428_ = lean_ctor_get_uint8(v___x_1412_, 16);
v_zetaUnused_1429_ = lean_ctor_get_uint8(v___x_1412_, 17);
v_zetaHave_1430_ = lean_ctor_get_uint8(v___x_1412_, 18);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1432_ = v___x_1412_;
v_isShared_1433_ = v_isSharedCheck_1489_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v___x_1412_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1489_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v_trackZetaDelta_1434_; lean_object* v_zetaDeltaSet_1435_; lean_object* v_lctx_1436_; lean_object* v_localInstances_1437_; lean_object* v_defEqCtx_x3f_1438_; lean_object* v_synthPendingDepth_1439_; lean_object* v_canUnfold_x3f_1440_; uint8_t v_univApprox_1441_; uint8_t v_inTypeClassResolution_1442_; uint8_t v_cacheInferType_1443_; uint8_t v___x_1444_; lean_object* v_config_1446_; 
v_trackZetaDelta_1434_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*7);
v_zetaDeltaSet_1435_ = lean_ctor_get(v___y_1405_, 1);
lean_inc(v_zetaDeltaSet_1435_);
v_lctx_1436_ = lean_ctor_get(v___y_1405_, 2);
lean_inc_ref(v_lctx_1436_);
v_localInstances_1437_ = lean_ctor_get(v___y_1405_, 3);
lean_inc_ref(v_localInstances_1437_);
v_defEqCtx_x3f_1438_ = lean_ctor_get(v___y_1405_, 4);
lean_inc(v_defEqCtx_x3f_1438_);
v_synthPendingDepth_1439_ = lean_ctor_get(v___y_1405_, 5);
lean_inc(v_synthPendingDepth_1439_);
v_canUnfold_x3f_1440_ = lean_ctor_get(v___y_1405_, 6);
lean_inc(v_canUnfold_x3f_1440_);
v_univApprox_1441_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1442_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*7 + 2);
v_cacheInferType_1443_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*7 + 3);
v___x_1444_ = 2;
if (v_isShared_1433_ == 0)
{
v_config_1446_ = v___x_1432_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 0, v_foApprox_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 1, v_ctxApprox_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 2, v_quasiPatternApprox_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 3, v_constApprox_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 4, v_isDefEqStuckEx_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 5, v_unificationHints_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 6, v_proofIrrelevance_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 7, v_assignSyntheticOpaque_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 8, v_offsetCnstrs_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 10, v_etaStruct_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 11, v_univApprox_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 12, v_iota_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 13, v_beta_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 14, v_proj_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 15, v_zeta_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 16, v_zetaDelta_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 17, v_zetaUnused_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, 18, v_zetaHave_1430_);
v_config_1446_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
uint64_t v___x_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1480_; 
lean_ctor_set_uint8(v_config_1446_, 9, v___x_1444_);
v___x_1447_ = l_Lean_Meta_Context_configKey(v___y_1405_);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___y_1405_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; 
v_unused_1481_ = lean_ctor_get(v___y_1405_, 6);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v___y_1405_, 5);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v___y_1405_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v___y_1405_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v___y_1405_, 2);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v___y_1405_, 1);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v___y_1405_, 0);
lean_dec(v_unused_1487_);
v___x_1449_ = v___y_1405_;
v_isShared_1450_ = v_isSharedCheck_1480_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___y_1405_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1480_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint64_t v___x_1451_; uint64_t v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v_key_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1451_ = 3ULL;
v___x_1452_ = lean_uint64_shift_right(v___x_1447_, v___x_1451_);
v___x_1453_ = l_Lean_Expr_mvarId_x21(v_a_1411_);
lean_dec(v_a_1411_);
v___x_1454_ = 1;
v___x_1455_ = lean_uint64_shift_left(v___x_1452_, v___x_1451_);
v___x_1456_ = lean_uint64_once(&l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0, &l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0);
v_key_1457_ = lean_uint64_lor(v___x_1455_, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1458_, 0, v_config_1446_);
lean_ctor_set_uint64(v___x_1458_, sizeof(void*)*1, v_key_1457_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1458_);
v___x_1460_ = v___x_1449_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_zetaDeltaSet_1435_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_lctx_1436_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_localInstances_1437_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_defEqCtx_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1479_, 5, v_synthPendingDepth_1439_);
lean_ctor_set(v_reuseFailAlloc_1479_, 6, v_canUnfold_x3f_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*7, v_trackZetaDelta_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*7 + 1, v_univApprox_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*7 + 3, v_cacheInferType_1443_);
v___x_1460_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_MVarId_refl(v___x_1453_, v___x_1454_, v___x_1460_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec_ref(v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1470_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_box(v___x_1454_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1461_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1461_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
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
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v___y_1405_);
v_a_1490_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1410_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1410_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_2362__boxed_1506_; lean_object* v_res_1507_; 
v___x_2362__boxed_1506_ = lean_unbox(v___x_1499_);
v_res_1507_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1498_, v___x_2362__boxed_1506_, v___x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1508_, lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_e_1509_);
v___x_1516_ = 0;
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_box(v___x_1516_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1519_, 0, v___x_1515_);
lean_closure_set(v___f_1519_, 1, v___x_1518_);
lean_closure_set(v___f_1519_, 2, v___x_1517_);
v___x_1520_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1520_, 0, lean_box(0));
lean_closure_set(v___x_1520_, 1, v_mctx_1508_);
lean_closure_set(v___x_1520_, 2, v___f_1519_);
v___x_1521_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1520_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1521_) == 0)
{
return v___x_1521_;
}
else
{
lean_object* v_a_1522_; uint8_t v___y_1524_; uint8_t v___x_1534_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
v___x_1534_ = l_Lean_Exception_isInterrupt(v_a_1522_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Lean_Exception_isRuntime(v_a_1522_);
v___y_1524_ = v___x_1535_;
goto v___jp_1523_;
}
else
{
lean_dec(v_a_1522_);
v___y_1524_ = v___x_1534_;
goto v___jp_1523_;
}
v___jp_1523_:
{
if (v___y_1524_ == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1532_; 
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1521_, 0);
lean_dec(v_unused_1533_);
v___x_1526_ = v___x_1521_;
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v___x_1521_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_box(v___y_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1536_, lean_object* v_e_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1536_, v_e_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_result_1550_; lean_object* v_eNew_1551_; lean_object* v___x_1552_; 
v_result_1550_ = lean_ctor_get(v_r_1544_, 2);
lean_inc_ref(v_result_1550_);
lean_dec_ref(v_r_1544_);
v_eNew_1551_ = lean_ctor_get(v_result_1550_, 0);
lean_inc_ref(v_eNew_1551_);
lean_dec_ref(v_result_1550_);
v___x_1552_ = l_Lean_Meta_ppExpr(v_eNew_1551_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1557_ = l_Std_Format_defWidth;
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = l_Std_Format_pretty(v_a_1553_, v___x_1557_, v___x_1558_, v___x_1558_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1559_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1564_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1552_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1552_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1579_){
_start:
{
switch(v_x_1579_)
{
case 0:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
return v___x_1580_;
}
case 1:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(1u);
return v___x_1581_;
}
default: 
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(2u);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1583_){
_start:
{
uint8_t v_x_boxed_1584_; lean_object* v_res_1585_; 
v_x_boxed_1584_ = lean_unbox(v_x_1583_);
v_res_1585_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1588_){
_start:
{
uint8_t v_x_4__boxed_1589_; lean_object* v_res_1590_; 
v_x_4__boxed_1589_ = lean_unbox(v_x_1588_);
v_res_1590_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1591_){
_start:
{
lean_inc(v_k_1591_);
return v_k_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1592_);
lean_dec(v_k_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1594_, lean_object* v_ctorIdx_1595_, uint8_t v_t_1596_, lean_object* v_h_1597_, lean_object* v_k_1598_){
_start:
{
lean_inc(v_k_1598_);
return v_k_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1599_, lean_object* v_ctorIdx_1600_, lean_object* v_t_1601_, lean_object* v_h_1602_, lean_object* v_k_1603_){
_start:
{
uint8_t v_t_boxed_1604_; lean_object* v_res_1605_; 
v_t_boxed_1604_ = lean_unbox(v_t_1601_);
v_res_1605_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1599_, v_ctorIdx_1600_, v_t_boxed_1604_, v_h_1602_, v_k_1603_);
lean_dec(v_k_1603_);
lean_dec(v_ctorIdx_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1606_){
_start:
{
lean_inc(v_none_1606_);
return v_none_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1607_);
lean_dec(v_none_1607_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1609_, uint8_t v_t_1610_, lean_object* v_h_1611_, lean_object* v_none_1612_){
_start:
{
lean_inc(v_none_1612_);
return v_none_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_none_1616_){
_start:
{
uint8_t v_t_boxed_1617_; lean_object* v_res_1618_; 
v_t_boxed_1617_ = lean_unbox(v_t_1614_);
v_res_1618_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1613_, v_t_boxed_1617_, v_h_1615_, v_none_1616_);
lean_dec(v_none_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1619_){
_start:
{
lean_inc(v_assumption_1619_);
return v_assumption_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1620_);
lean_dec(v_assumption_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1622_, uint8_t v_t_1623_, lean_object* v_h_1624_, lean_object* v_assumption_1625_){
_start:
{
lean_inc(v_assumption_1625_);
return v_assumption_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_assumption_1629_){
_start:
{
uint8_t v_t_boxed_1630_; lean_object* v_res_1631_; 
v_t_boxed_1630_ = lean_unbox(v_t_1627_);
v_res_1631_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1626_, v_t_boxed_1630_, v_h_1628_, v_assumption_1629_);
lean_dec(v_assumption_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1632_){
_start:
{
lean_inc(v_solveByElim_1632_);
return v_solveByElim_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1633_);
lean_dec(v_solveByElim_1633_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1635_, uint8_t v_t_1636_, lean_object* v_h_1637_, lean_object* v_solveByElim_1638_){
_start:
{
lean_inc(v_solveByElim_1638_);
return v_solveByElim_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1639_, lean_object* v_t_1640_, lean_object* v_h_1641_, lean_object* v_solveByElim_1642_){
_start:
{
uint8_t v_t_boxed_1643_; lean_object* v_res_1644_; 
v_t_boxed_1643_ = lean_unbox(v_t_1640_);
v_res_1644_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1639_, v_t_boxed_1643_, v_h_1641_, v_solveByElim_1642_);
lean_dec(v_solveByElim_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1654_, v_x_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v_x_1655_);
lean_dec(v_x_1654_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = 0;
v___x_1669_ = lean_box(v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v_x_1671_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v_env_1685_; lean_object* v___x_1686_; lean_object* v_mctx_1687_; lean_object* v_lctx_1688_; lean_object* v_options_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1684_ = lean_st_ref_get(v___y_1682_);
v_env_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc_ref(v_env_1685_);
lean_dec(v___x_1684_);
v___x_1686_ = lean_st_ref_get(v___y_1680_);
v_mctx_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc_ref(v_mctx_1687_);
lean_dec(v___x_1686_);
v_lctx_1688_ = lean_ctor_get(v___y_1679_, 2);
v_options_1689_ = lean_ctor_get(v___y_1681_, 2);
lean_inc_ref(v_options_1689_);
lean_inc_ref(v_lctx_1688_);
v___x_1690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1690_, 0, v_env_1685_);
lean_ctor_set(v___x_1690_, 1, v_mctx_1687_);
lean_ctor_set(v___x_1690_, 2, v_lctx_1688_);
lean_ctor_set(v___x_1690_, 3, v_options_1689_);
v___x_1691_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_msgData_1678_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_ref_1706_; lean_object* v___x_1707_; lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_ref_1706_ = lean_ctor_get(v___y_1703_, 5);
v___x_1707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_inc(v_ref_1706_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_ref_1706_);
lean_ctor_set(v___x_1712_, 1, v_a_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1734_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1733_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_x_1735_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1751_, lean_object* v_depth_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___f_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v_cfg_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___f_1758_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1759_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1760_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1761_ = 0;
v___x_1762_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1762_, 0, v_depth_1752_);
lean_ctor_set(v___x_1762_, 1, v___f_1758_);
lean_ctor_set(v___x_1762_, 2, v___f_1759_);
lean_ctor_set(v___x_1762_, 3, v___f_1760_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*4, v___x_1761_);
v___x_1763_ = 1;
v___x_1764_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1765_ = 1;
v___x_1766_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1766_, 0, v___x_1762_);
lean_ctor_set(v___x_1766_, 1, v___x_1764_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2, v___x_1765_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 1, v___x_1763_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 2, v___x_1761_);
v_cfg_1767_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1767_, 0, v___x_1766_);
lean_ctor_set_uint8(v_cfg_1767_, sizeof(void*)*1, v___x_1763_);
lean_ctor_set_uint8(v_cfg_1767_, sizeof(void*)*1 + 1, v___x_1763_);
lean_ctor_set_uint8(v_cfg_1767_, sizeof(void*)*1 + 2, v___x_1763_);
lean_ctor_set_uint8(v_cfg_1767_, sizeof(void*)*1 + 3, v___x_1761_);
v___x_1768_ = lean_box(0);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1770_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1761_, v___x_1761_, v___x_1768_, v___x_1768_, v___x_1769_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1774_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_fst_1772_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v_a_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec(v_a_1771_);
v___x_1774_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1767_, v_fst_1772_, v_snd_1773_, v_goals_1751_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1785_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
if (lean_obj_tag(v_a_1775_) == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_del_object(v___x_1777_);
lean_dec(v_a_1775_);
v___x_1783_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1784_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1783_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1774_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1774_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref_known(v_cfg_1767_, 1);
lean_dec(v_goals_1751_);
v_a_1794_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1770_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1770_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1802_, lean_object* v_depth_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1802_, v_depth_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1810_, lean_object* v_msg_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1818_, v_msg_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Lean_Expr_hasMVar(v_e_1826_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_e_1826_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v_mctx_1832_; lean_object* v___x_1833_; lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1836_; lean_object* v_cache_1837_; lean_object* v_zetaDeltaFVarIds_1838_; lean_object* v_postponed_1839_; lean_object* v_diag_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1849_; 
v___x_1831_ = lean_st_ref_get(v___y_1827_);
v_mctx_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_ref(v_mctx_1832_);
lean_dec(v___x_1831_);
v___x_1833_ = l_Lean_instantiateMVarsCore(v_mctx_1832_, v_e_1826_);
v_fst_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_fst_1834_);
v_snd_1835_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_snd_1835_);
lean_dec_ref(v___x_1833_);
v___x_1836_ = lean_st_ref_take(v___y_1827_);
v_cache_1837_ = lean_ctor_get(v___x_1836_, 1);
v_zetaDeltaFVarIds_1838_ = lean_ctor_get(v___x_1836_, 2);
v_postponed_1839_ = lean_ctor_get(v___x_1836_, 3);
v_diag_1840_ = lean_ctor_get(v___x_1836_, 4);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v___x_1836_, 0);
lean_dec(v_unused_1850_);
v___x_1842_ = v___x_1836_;
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_diag_1840_);
lean_inc(v_postponed_1839_);
lean_inc(v_zetaDeltaFVarIds_1838_);
lean_inc(v_cache_1837_);
lean_dec(v___x_1836_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_snd_1835_);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_snd_1835_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_cache_1837_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_zetaDeltaFVarIds_1838_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_postponed_1839_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_diag_1840_);
v___x_1845_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_st_ref_set(v___y_1827_, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_fst_1834_);
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1851_, v___y_1852_);
lean_dec(v___y_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1855_, v___y_1857_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1869_; double v___x_1870_; 
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_float_of_nat(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1874_, lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_ref_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1927_; 
v_ref_1881_ = lean_ctor_get(v___y_1878_, 5);
v___x_1882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1927_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1927_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v_traceState_1888_; lean_object* v_env_1889_; lean_object* v_nextMacroScope_1890_; lean_object* v_ngen_1891_; lean_object* v_auxDeclNGen_1892_; lean_object* v_cache_1893_; lean_object* v_messages_1894_; lean_object* v_infoState_1895_; lean_object* v_snapshotTasks_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1926_; 
v___x_1887_ = lean_st_ref_take(v___y_1879_);
v_traceState_1888_ = lean_ctor_get(v___x_1887_, 4);
v_env_1889_ = lean_ctor_get(v___x_1887_, 0);
v_nextMacroScope_1890_ = lean_ctor_get(v___x_1887_, 1);
v_ngen_1891_ = lean_ctor_get(v___x_1887_, 2);
v_auxDeclNGen_1892_ = lean_ctor_get(v___x_1887_, 3);
v_cache_1893_ = lean_ctor_get(v___x_1887_, 5);
v_messages_1894_ = lean_ctor_get(v___x_1887_, 6);
v_infoState_1895_ = lean_ctor_get(v___x_1887_, 7);
v_snapshotTasks_1896_ = lean_ctor_get(v___x_1887_, 8);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1898_ = v___x_1887_;
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snapshotTasks_1896_);
lean_inc(v_infoState_1895_);
lean_inc(v_messages_1894_);
lean_inc(v_cache_1893_);
lean_inc(v_traceState_1888_);
lean_inc(v_auxDeclNGen_1892_);
lean_inc(v_ngen_1891_);
lean_inc(v_nextMacroScope_1890_);
lean_inc(v_env_1889_);
lean_dec(v___x_1887_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
uint64_t v_tid_1900_; lean_object* v_traces_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1925_; 
v_tid_1900_ = lean_ctor_get_uint64(v_traceState_1888_, sizeof(void*)*1);
v_traces_1901_ = lean_ctor_get(v_traceState_1888_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_traceState_1888_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1903_ = v_traceState_1888_;
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_traces_1901_);
lean_dec(v_traceState_1888_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; double v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1907_ = 0;
v___x_1908_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1909_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1909_, 0, v_cls_1874_);
lean_ctor_set(v___x_1909_, 1, v___x_1905_);
lean_ctor_set(v___x_1909_, 2, v___x_1908_);
lean_ctor_set_float(v___x_1909_, sizeof(void*)*3, v___x_1906_);
lean_ctor_set_float(v___x_1909_, sizeof(void*)*3 + 8, v___x_1906_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*3 + 16, v___x_1907_);
v___x_1910_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1911_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v_a_1883_);
lean_ctor_set(v___x_1911_, 2, v___x_1910_);
lean_inc(v_ref_1881_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_ref_1881_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l_Lean_PersistentArray_push___redArg(v_traces_1901_, v___x_1912_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1913_);
v___x_1915_ = v___x_1903_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1913_);
lean_ctor_set_uint64(v_reuseFailAlloc_1924_, sizeof(void*)*1, v_tid_1900_);
v___x_1915_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 4, v___x_1915_);
v___x_1917_ = v___x_1898_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_env_1889_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_nextMacroScope_1890_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_ngen_1891_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_auxDeclNGen_1892_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_cache_1893_);
lean_ctor_set(v_reuseFailAlloc_1923_, 6, v_messages_1894_);
lean_ctor_set(v_reuseFailAlloc_1923_, 7, v_infoState_1895_);
lean_ctor_set(v_reuseFailAlloc_1923_, 8, v_snapshotTasks_1896_);
v___x_1917_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1918_ = lean_st_ref_set(v___y_1879_, v___x_1917_);
v___x_1919_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1919_);
v___x_1921_ = v___x_1885_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1928_, v_msg_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1936_, lean_object* v_x_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = l_List_reverse___redArg(v_x_1937_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v_head_1945_; lean_object* v_tail_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1964_; 
v_head_1945_ = lean_ctor_get(v_x_1936_, 0);
v_tail_1946_ = lean_ctor_get(v_x_1936_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_x_1936_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1948_ = v_x_1936_;
v_isShared_1949_ = v_isSharedCheck_1964_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_tail_1946_);
lean_inc(v_head_1945_);
lean_dec(v_x_1936_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1964_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_MVarId_assumption(v_head_1945_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v_x_1937_);
lean_ctor_set(v___x_1948_, 0, v_a_1951_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1951_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_x_1937_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v_x_1936_ = v_tail_1946_;
v_x_1937_ = v___x_1953_;
goto _start;
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1948_);
lean_dec(v_tail_1946_);
lean_dec(v_x_1937_);
v_a_1956_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1950_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1950_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1965_, v_x_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1986_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1987_ = l_Lean_Name_append(v___x_1986_, v___x_1985_);
return v___x_1987_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1992_, lean_object* v_goal_1993_, lean_object* v_target_1994_, uint8_t v_symm_1995_, uint8_t v_side_1996_, lean_object* v_lem_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; uint8_t v___y_2008_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v_fst_2035_; uint8_t v_snd_2036_; lean_object* v___y_2060_; uint8_t v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2119_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v_val_2217_; 
if (lean_obj_tag(v_lem_1997_) == 0)
{
lean_object* v_val_2227_; 
v_val_2227_ = lean_ctor_get(v_lem_1997_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v_lem_1997_, 1);
v_val_2217_ = v_val_2227_;
goto v___jp_2216_;
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2229_; 
v_val_2228_ = lean_ctor_get(v_lem_1997_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v_lem_1997_, 1);
v___x_2229_ = l_Lean_Meta_saveState___redArg(v___y_1999_, v___y_2001_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2228_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; 
lean_dec(v_a_2230_);
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v_val_2217_ = v_a_2232_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_target_1994_);
lean_dec(v_goal_1993_);
lean_dec(v_weight_1992_);
v_a_2233_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2262_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2262_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
uint8_t v___y_2238_; uint8_t v___x_2260_; 
v___x_2260_ = l_Lean_Exception_isInterrupt(v_a_2233_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; 
lean_inc(v_a_2233_);
v___x_2261_ = l_Lean_Exception_isRuntime(v_a_2233_);
v___y_2238_ = v___x_2261_;
goto v___jp_2237_;
}
else
{
v___y_2238_ = v___x_2260_;
goto v___jp_2237_;
}
v___jp_2237_:
{
if (v___y_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_del_object(v___x_2235_);
lean_dec(v_a_2233_);
v___x_2239_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2230_, v___y_1999_, v___y_2001_);
lean_dec(v_a_2230_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2247_; 
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2239_, 0);
lean_dec(v_unused_2248_);
v___x_2241_ = v___x_2239_;
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v___x_2239_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2243_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_a_2249_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2239_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2239_);
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
else
{
lean_object* v___x_2258_; 
lean_dec(v_a_2230_);
if (v_isShared_2236_ == 0)
{
v___x_2258_ = v___x_2235_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2233_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_val_2228_);
lean_dec_ref(v_target_1994_);
lean_dec(v_goal_1993_);
lean_dec(v_weight_1992_);
v_a_2263_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2229_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2229_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
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
v___jp_2003_:
{
if (v___y_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v___y_2006_);
v___x_2009_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2005_, v___y_2007_, v___y_2004_);
lean_dec_ref(v___y_2005_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_2009_, 0);
lean_dec(v_unused_2018_);
v___x_2011_ = v___x_2009_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_dec(v___x_2009_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2013_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_a_2019_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2009_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2009_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; 
lean_dec_ref(v___y_2005_);
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___y_2006_);
return v___x_2027_;
}
}
v___jp_2028_:
{
lean_object* v___x_2037_; lean_object* v_mctx_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_st_ref_get(v___y_2034_);
v_mctx_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref_n(v_mctx_2038_, 2);
lean_dec(v___x_2037_);
v___x_2039_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2038_, v___y_2032_, v___y_2031_, v___y_2034_, v___y_2030_, v___y_2033_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2044_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2044_, 0, v_fst_2035_);
lean_ctor_set(v___x_2044_, 1, v_weight_1992_);
lean_ctor_set(v___x_2044_, 2, v___y_2029_);
lean_ctor_set(v___x_2044_, 3, v_mctx_2038_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*4, v_snd_2036_);
v___x_2045_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*4 + 1, v___x_2045_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2046_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_mctx_2038_);
lean_dec_ref(v_fst_2035_);
lean_dec_ref(v___y_2029_);
lean_dec(v_weight_1992_);
v_a_2051_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2039_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2039_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
v___jp_2059_:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2060_);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2069_, v___y_2065_);
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2070_);
v___x_2072_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2073_ = lean_unsigned_to_nat(4u);
v___x_2074_ = l_Lean_Expr_isAppOfArity(v_a_2071_, v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
v___y_2029_ = v___y_2060_;
v___y_2030_ = v___y_2066_;
v___y_2031_ = v___y_2064_;
v___y_2032_ = v___y_2062_;
v___y_2033_ = v___y_2067_;
v___y_2034_ = v___y_2065_;
v_fst_2035_ = v_a_2071_;
v_snd_2036_ = v___y_2061_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = lean_unsigned_to_nat(3u);
v___x_2076_ = l_Lean_Expr_getAppNumArgs(v_a_2071_);
v___x_2077_ = lean_nat_sub(v___x_2076_, v___x_2075_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_unsigned_to_nat(1u);
v___x_2079_ = lean_nat_sub(v___x_2077_, v___x_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = l_Lean_Expr_getRevArg_x21(v_a_2071_, v___x_2079_);
lean_dec(v_a_2071_);
v___y_2029_ = v___y_2060_;
v___y_2030_ = v___y_2066_;
v___y_2031_ = v___y_2064_;
v___y_2032_ = v___y_2062_;
v___y_2033_ = v___y_2067_;
v___y_2034_ = v___y_2065_;
v_fst_2035_ = v___x_2080_;
v_snd_2036_ = v___y_2063_;
goto v___jp_2028_;
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v___x_2068_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v___y_2060_);
lean_dec(v_weight_1992_);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
v___jp_2086_:
{
if (v___y_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v___y_2089_);
v___x_2092_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2087_, v___y_2090_, v___y_2088_);
lean_dec_ref(v___y_2087_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
goto v___jp_2083_;
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
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
else
{
lean_object* v___x_2101_; 
lean_dec_ref(v___y_2087_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___y_2089_);
return v___x_2101_;
}
}
v___jp_2102_:
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec_ref(v___y_2104_);
v___x_2108_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2105_, v___y_2106_, v___y_2103_);
lean_dec_ref(v___y_2105_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_dec_ref_known(v___x_2108_, 1);
goto v___jp_2083_;
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; 
lean_dec_ref(v___y_2105_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___y_2104_);
return v___x_2117_;
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_saveState___redArg(v___y_1999_, v___y_2001_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = 1;
v___x_2123_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2119_);
v___x_2124_ = l_Lean_MVarId_rewrite(v_goal_1993_, v_target_1994_, v___y_2119_, v_symm_1995_, v___x_2123_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2121_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2186_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2186_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_eNew_2129_; lean_object* v_mvarIds_2130_; uint8_t v___x_2131_; 
v_eNew_2129_ = lean_ctor_get(v_a_2125_, 0);
v_mvarIds_2130_ = lean_ctor_get(v_a_2125_, 2);
v___x_2131_ = l_List_isEmpty___redArg(v_mvarIds_2130_);
if (v___x_2131_ == 0)
{
lean_inc_ref(v_eNew_2129_);
lean_del_object(v___x_2127_);
lean_dec_ref(v___y_2119_);
switch(v_side_1996_)
{
case 0:
{
if (v___x_2131_ == 0)
{
lean_dec_ref(v_eNew_2129_);
lean_dec(v_a_2125_);
lean_dec(v_weight_1992_);
goto v___jp_2083_;
}
else
{
v___y_2060_ = v_a_2125_;
v___y_2061_ = v___x_2131_;
v___y_2062_ = v_eNew_2129_;
v___y_2063_ = v___x_2122_;
v___y_2064_ = v___y_1998_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
goto v___jp_2059_;
}
}
case 1:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Meta_saveState___redArg(v___y_1999_, v___y_2001_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = lean_box(0);
lean_inc(v_mvarIds_2130_);
v___x_2135_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2130_, v___x_2134_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref_known(v___x_2135_, 1);
lean_dec(v_a_2133_);
v___y_2060_ = v_a_2125_;
v___y_2061_ = v___x_2131_;
v___y_2062_ = v_eNew_2129_;
v___y_2063_ = v___x_2122_;
v___y_2064_ = v___y_1998_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2136_; uint8_t v___x_2137_; 
lean_dec_ref(v_eNew_2129_);
lean_dec(v_a_2125_);
lean_dec(v_weight_1992_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Exception_isInterrupt(v_a_2136_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2138_; 
lean_inc(v_a_2136_);
v___x_2138_ = l_Lean_Exception_isRuntime(v_a_2136_);
v___y_2103_ = v___y_2001_;
v___y_2104_ = v_a_2136_;
v___y_2105_ = v_a_2133_;
v___y_2106_ = v___y_1999_;
v___y_2107_ = v___x_2138_;
goto v___jp_2102_;
}
else
{
v___y_2103_ = v___y_2001_;
v___y_2104_ = v_a_2136_;
v___y_2105_ = v_a_2133_;
v___y_2106_ = v___y_1999_;
v___y_2107_ = v___x_2137_;
goto v___jp_2102_;
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_eNew_2129_);
lean_dec(v_a_2125_);
lean_dec(v_weight_1992_);
v_a_2139_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2132_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2132_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
default: 
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Meta_saveState___redArg(v___y_1999_, v___y_2001_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2130_);
v___x_2150_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2130_, v___x_2149_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
lean_dec(v_a_2148_);
v___y_2060_ = v_a_2125_;
v___y_2061_ = v___x_2131_;
v___y_2062_ = v_eNew_2129_;
v___y_2063_ = v___x_2122_;
v___y_2064_ = v___y_1998_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2151_; uint8_t v___x_2152_; 
lean_dec_ref(v_eNew_2129_);
lean_dec(v_a_2125_);
lean_dec(v_weight_1992_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l_Lean_Exception_isInterrupt(v_a_2151_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
lean_inc(v_a_2151_);
v___x_2153_ = l_Lean_Exception_isRuntime(v_a_2151_);
v___y_2087_ = v_a_2148_;
v___y_2088_ = v___y_2001_;
v___y_2089_ = v_a_2151_;
v___y_2090_ = v___y_1999_;
v___y_2091_ = v___x_2153_;
goto v___jp_2086_;
}
else
{
v___y_2087_ = v_a_2148_;
v___y_2088_ = v___y_2001_;
v___y_2089_ = v_a_2151_;
v___y_2090_ = v___y_1999_;
v___y_2091_ = v___x_2152_;
goto v___jp_2086_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_eNew_2129_);
lean_dec(v_a_2125_);
lean_dec(v_weight_1992_);
v_a_2154_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2147_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2147_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v_mctx_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_st_ref_get(v___y_1999_);
v_mctx_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref_n(v_mctx_2163_, 2);
lean_dec(v___x_2162_);
lean_inc_ref(v_eNew_2129_);
v___x_2164_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2163_, v_eNew_2129_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2177_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2177_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2177_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2172_; 
v___x_2169_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2169_, 0, v___y_2119_);
lean_ctor_set(v___x_2169_, 1, v_weight_1992_);
lean_ctor_set(v___x_2169_, 2, v_a_2125_);
lean_ctor_set(v___x_2169_, 3, v_mctx_2163_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*4, v_symm_1995_);
v___x_2170_ = lean_unbox(v_a_2165_);
lean_dec(v_a_2165_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*4 + 1, v___x_2170_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 1);
lean_ctor_set(v___x_2127_, 0, v___x_2169_);
v___x_2172_ = v___x_2127_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2169_);
v___x_2172_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2172_);
v___x_2174_ = v___x_2167_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_mctx_2163_);
lean_del_object(v___x_2127_);
lean_dec(v_a_2125_);
lean_dec_ref(v___y_2119_);
lean_dec(v_weight_1992_);
v_a_2178_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2164_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2164_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
else
{
lean_object* v_a_2187_; uint8_t v___x_2188_; 
lean_dec_ref(v___y_2119_);
lean_dec(v_weight_1992_);
v_a_2187_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2188_ = l_Lean_Exception_isInterrupt(v_a_2187_);
if (v___x_2188_ == 0)
{
uint8_t v___x_2189_; 
lean_inc(v_a_2187_);
v___x_2189_ = l_Lean_Exception_isRuntime(v_a_2187_);
v___y_2004_ = v___y_2001_;
v___y_2005_ = v_a_2121_;
v___y_2006_ = v_a_2187_;
v___y_2007_ = v___y_1999_;
v___y_2008_ = v___x_2189_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2001_;
v___y_2005_ = v_a_2121_;
v___y_2006_ = v_a_2187_;
v___y_2007_ = v___y_1999_;
v___y_2008_ = v___x_2188_;
goto v___jp_2003_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_target_1994_);
lean_dec(v_goal_1993_);
lean_dec(v_weight_1992_);
v_a_2190_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2120_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2120_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
v___jp_2198_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_inc_ref(v___y_2202_);
v___x_2203_ = l_Lean_stringToMessageData(v___y_2202_);
lean_inc_ref(v___y_2199_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___y_2199_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc_ref(v___y_2200_);
v___x_2205_ = l_Lean_MessageData_ofExpr(v___y_2200_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
lean_inc(v___y_2201_);
v___x_2207_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2201_, v___x_2206_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref_known(v___x_2207_, 1);
v___y_2119_ = v___y_2200_;
goto v___jp_2118_;
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_target_1994_);
lean_dec(v_goal_1993_);
lean_dec(v_weight_1992_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
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
v___jp_2216_:
{
lean_object* v_options_2218_; uint8_t v_hasTrace_2219_; 
v_options_2218_ = lean_ctor_get(v___y_2000_, 2);
v_hasTrace_2219_ = lean_ctor_get_uint8(v_options_2218_, sizeof(void*)*1);
if (v_hasTrace_2219_ == 0)
{
v___y_2119_ = v_val_2217_;
goto v___jp_2118_;
}
else
{
lean_object* v_inheritedTraceOptions_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_inheritedTraceOptions_2220_ = lean_ctor_get(v___y_2000_, 13);
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2222_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2220_, v_options_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
v___y_2119_ = v_val_2217_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1995_ == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2199_ = v___x_2224_;
v___y_2200_ = v_val_2217_;
v___y_2201_ = v___x_2221_;
v___y_2202_ = v___x_2225_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2199_ = v___x_2224_;
v___y_2200_ = v_val_2217_;
v___y_2201_ = v___x_2221_;
v___y_2202_ = v___x_2226_;
goto v___jp_2198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2271_, lean_object* v_goal_2272_, lean_object* v_target_2273_, lean_object* v_symm_2274_, lean_object* v_side_2275_, lean_object* v_lem_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_symm_boxed_2282_; uint8_t v_side_boxed_2283_; lean_object* v_res_2284_; 
v_symm_boxed_2282_ = lean_unbox(v_symm_2274_);
v_side_boxed_2283_ = lean_unbox(v_side_2275_);
v_res_2284_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2271_, v_goal_2272_, v_target_2273_, v_symm_boxed_2282_, v_side_boxed_2283_, v_lem_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2285_, lean_object* v_goal_2286_, lean_object* v_target_2287_, uint8_t v_side_2288_, lean_object* v_lem_2289_, uint8_t v_symm_2290_, lean_object* v_weight_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; 
v___x_2297_ = lean_box(v_symm_2290_);
v___x_2298_ = lean_box(v_side_2288_);
v___f_2299_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2299_, 0, v_weight_2291_);
lean_closure_set(v___f_2299_, 1, v_goal_2286_);
lean_closure_set(v___f_2299_, 2, v_target_2287_);
lean_closure_set(v___f_2299_, 3, v___x_2297_);
lean_closure_set(v___f_2299_, 4, v___x_2298_);
lean_closure_set(v___f_2299_, 5, v_lem_2289_);
v___x_2300_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2285_, v___f_2299_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2301_, lean_object* v_goal_2302_, lean_object* v_target_2303_, lean_object* v_side_2304_, lean_object* v_lem_2305_, lean_object* v_symm_2306_, lean_object* v_weight_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
uint8_t v_side_boxed_2313_; uint8_t v_symm_boxed_2314_; lean_object* v_res_2315_; 
v_side_boxed_2313_ = lean_unbox(v_side_2304_);
v_symm_boxed_2314_ = lean_unbox(v_symm_2306_);
v_res_2315_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2301_, v_goal_2302_, v_target_2303_, v_side_boxed_2313_, v_lem_2305_, v_symm_boxed_2314_, v_weight_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2316_, lean_object* v_k_2317_, uint8_t v_cleanupAnnotations_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___f_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___f_2324_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2324_, 0, v_k_2317_);
v___x_2325_ = 0;
v___x_2326_ = lean_box(0);
v___x_2327_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2325_, v___x_2326_, v_type_2316_, v___f_2324_, v_cleanupAnnotations_2318_, v___x_2325_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_a_2336_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2327_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2327_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2344_, lean_object* v_k_2345_, lean_object* v_cleanupAnnotations_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2352_; lean_object* v_res_2353_; 
v_cleanupAnnotations_boxed_2352_ = lean_unbox(v_cleanupAnnotations_2346_);
v_res_2353_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2344_, v_k_2345_, v_cleanupAnnotations_boxed_2352_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2354_, lean_object* v_type_2355_, lean_object* v_k_2356_, uint8_t v_cleanupAnnotations_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2355_, v_k_2356_, v_cleanupAnnotations_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_type_2365_, lean_object* v_k_2366_, lean_object* v_cleanupAnnotations_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2373_; lean_object* v_res_2374_; 
v_cleanupAnnotations_boxed_2373_ = lean_unbox(v_cleanupAnnotations_2367_);
v_res_2374_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2364_, v_type_2365_, v_k_2366_, v_cleanupAnnotations_boxed_2373_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2375_, lean_object* v_k_2376_, uint8_t v_cleanupAnnotations_2377_, uint8_t v_preserveNondepLet_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___f_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2384_, 0, v_k_2376_);
v___x_2385_ = 1;
v___x_2386_ = 0;
v___x_2387_ = lean_box(0);
v___x_2388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2375_, v___x_2385_, v___x_2385_, v_preserveNondepLet_2378_, v___x_2386_, v___x_2387_, v___f_2384_, v_cleanupAnnotations_2377_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2388_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2388_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2405_, lean_object* v_k_2406_, lean_object* v_cleanupAnnotations_2407_, lean_object* v_preserveNondepLet_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2414_; uint8_t v_preserveNondepLet_boxed_2415_; lean_object* v_res_2416_; 
v_cleanupAnnotations_boxed_2414_ = lean_unbox(v_cleanupAnnotations_2407_);
v_preserveNondepLet_boxed_2415_ = lean_unbox(v_preserveNondepLet_2408_);
v_res_2416_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2405_, v_k_2406_, v_cleanupAnnotations_boxed_2414_, v_preserveNondepLet_boxed_2415_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2417_, lean_object* v_e_2418_, lean_object* v_k_2419_, uint8_t v_cleanupAnnotations_2420_, uint8_t v_preserveNondepLet_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2418_, v_k_2419_, v_cleanupAnnotations_2420_, v_preserveNondepLet_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_e_2429_, lean_object* v_k_2430_, lean_object* v_cleanupAnnotations_2431_, lean_object* v_preserveNondepLet_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2438_; uint8_t v_preserveNondepLet_boxed_2439_; lean_object* v_res_2440_; 
v_cleanupAnnotations_boxed_2438_ = lean_unbox(v_cleanupAnnotations_2431_);
v_preserveNondepLet_boxed_2439_ = lean_unbox(v_preserveNondepLet_2432_);
v_res_2440_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2428_, v_e_2429_, v_k_2430_, v_cleanupAnnotations_boxed_2438_, v_preserveNondepLet_boxed_2439_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2441_, lean_object* v_e_x27_2442_, lean_object* v_a_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2446_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc_ref(v_e_x27_2442_);
v___x_2449_ = lean_apply_7(v_f_2441_, v_a_2443_, v_e_x27_2442_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, lean_box(0));
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2458_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_e_x27_2442_);
lean_ctor_set(v___x_2454_, 1, v_a_2450_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v_e_x27_2442_);
v_a_2459_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2449_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2449_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2467_, lean_object* v_e_x27_2468_, lean_object* v_a_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2467_, v_e_x27_2468_, v_a_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
switch(lean_obj_tag(v_x_2477_))
{
case 7:
{
lean_object* v_binderName_2484_; lean_object* v_binderType_2485_; lean_object* v_body_2486_; uint8_t v_binderInfo_2487_; lean_object* v___x_2488_; 
v_binderName_2484_ = lean_ctor_get(v_x_2477_, 0);
v_binderType_2485_ = lean_ctor_get(v_x_2477_, 1);
v_body_2486_ = lean_ctor_get(v_x_2477_, 2);
v_binderInfo_2487_ = lean_ctor_get_uint8(v_x_2477_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2485_);
lean_inc_ref(v_f_2476_);
v___x_2488_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_binderType_2485_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2492_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v_fst_2490_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_fst_2490_);
v_snd_2491_ = lean_ctor_get(v_a_2489_, 1);
lean_inc(v_snd_2491_);
lean_dec(v_a_2489_);
lean_inc_ref(v_body_2486_);
v___x_2492_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_body_2486_, v_snd_2491_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2522_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2522_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2522_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2521_; 
v_fst_2497_ = lean_ctor_get(v_a_2493_, 0);
v_snd_2498_ = lean_ctor_get(v_a_2493_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2500_ = v_a_2493_;
v_isShared_2501_ = v_isSharedCheck_2521_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snd_2498_);
lean_inc(v_fst_2497_);
lean_dec(v_a_2493_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2521_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___y_2503_; uint8_t v___y_2511_; size_t v___x_2515_; size_t v___x_2516_; uint8_t v___x_2517_; 
v___x_2515_ = lean_ptr_addr(v_binderType_2485_);
v___x_2516_ = lean_ptr_addr(v_fst_2490_);
v___x_2517_ = lean_usize_dec_eq(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
v___y_2511_ = v___x_2517_;
goto v___jp_2510_;
}
else
{
size_t v___x_2518_; size_t v___x_2519_; uint8_t v___x_2520_; 
v___x_2518_ = lean_ptr_addr(v_body_2486_);
v___x_2519_ = lean_ptr_addr(v_fst_2497_);
v___x_2520_ = lean_usize_dec_eq(v___x_2518_, v___x_2519_);
v___y_2511_ = v___x_2520_;
goto v___jp_2510_;
}
v___jp_2502_:
{
lean_object* v___x_2505_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___y_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___y_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_snd_2498_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2505_);
v___x_2507_ = v___x_2495_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
v___jp_2510_:
{
if (v___y_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_inc(v_binderName_2484_);
lean_dec_ref_known(v_x_2477_, 3);
v___x_2512_ = l_Lean_Expr_forallE___override(v_binderName_2484_, v_fst_2490_, v_fst_2497_, v_binderInfo_2487_);
v___y_2503_ = v___x_2512_;
goto v___jp_2502_;
}
else
{
uint8_t v___x_2513_; 
v___x_2513_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2487_, v_binderInfo_2487_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
lean_inc(v_binderName_2484_);
lean_dec_ref_known(v_x_2477_, 3);
v___x_2514_ = l_Lean_Expr_forallE___override(v_binderName_2484_, v_fst_2490_, v_fst_2497_, v_binderInfo_2487_);
v___y_2503_ = v___x_2514_;
goto v___jp_2502_;
}
else
{
lean_dec(v_fst_2497_);
lean_dec(v_fst_2490_);
v___y_2503_ = v_x_2477_;
goto v___jp_2502_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2490_);
lean_dec_ref_known(v_x_2477_, 3);
return v___x_2492_;
}
}
else
{
lean_dec_ref_known(v_x_2477_, 3);
lean_dec_ref(v_f_2476_);
return v___x_2488_;
}
}
case 6:
{
lean_object* v_binderName_2523_; lean_object* v_binderType_2524_; lean_object* v_body_2525_; uint8_t v_binderInfo_2526_; lean_object* v___x_2527_; 
v_binderName_2523_ = lean_ctor_get(v_x_2477_, 0);
v_binderType_2524_ = lean_ctor_get(v_x_2477_, 1);
v_body_2525_ = lean_ctor_get(v_x_2477_, 2);
v_binderInfo_2526_ = lean_ctor_get_uint8(v_x_2477_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2524_);
lean_inc_ref(v_f_2476_);
v___x_2527_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_binderType_2524_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v_fst_2529_; lean_object* v_snd_2530_; lean_object* v___x_2531_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v_fst_2529_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_fst_2529_);
v_snd_2530_ = lean_ctor_get(v_a_2528_, 1);
lean_inc(v_snd_2530_);
lean_dec(v_a_2528_);
lean_inc_ref(v_body_2525_);
v___x_2531_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_body_2525_, v_snd_2530_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2561_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2561_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2561_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_fst_2536_; lean_object* v_snd_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2560_; 
v_fst_2536_ = lean_ctor_get(v_a_2532_, 0);
v_snd_2537_ = lean_ctor_get(v_a_2532_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2532_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2539_ = v_a_2532_;
v_isShared_2540_ = v_isSharedCheck_2560_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snd_2537_);
lean_inc(v_fst_2536_);
lean_dec(v_a_2532_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2560_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___y_2542_; uint8_t v___y_2550_; size_t v___x_2554_; size_t v___x_2555_; uint8_t v___x_2556_; 
v___x_2554_ = lean_ptr_addr(v_binderType_2524_);
v___x_2555_ = lean_ptr_addr(v_fst_2529_);
v___x_2556_ = lean_usize_dec_eq(v___x_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
v___y_2550_ = v___x_2556_;
goto v___jp_2549_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = lean_ptr_addr(v_body_2525_);
v___x_2558_ = lean_ptr_addr(v_fst_2536_);
v___x_2559_ = lean_usize_dec_eq(v___x_2557_, v___x_2558_);
v___y_2550_ = v___x_2559_;
goto v___jp_2549_;
}
v___jp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___y_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___y_2542_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_snd_2537_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2544_);
v___x_2546_ = v___x_2534_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
v___jp_2549_:
{
if (v___y_2550_ == 0)
{
lean_object* v___x_2551_; 
lean_inc(v_binderName_2523_);
lean_dec_ref_known(v_x_2477_, 3);
v___x_2551_ = l_Lean_Expr_lam___override(v_binderName_2523_, v_fst_2529_, v_fst_2536_, v_binderInfo_2526_);
v___y_2542_ = v___x_2551_;
goto v___jp_2541_;
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2526_, v_binderInfo_2526_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
lean_inc(v_binderName_2523_);
lean_dec_ref_known(v_x_2477_, 3);
v___x_2553_ = l_Lean_Expr_lam___override(v_binderName_2523_, v_fst_2529_, v_fst_2536_, v_binderInfo_2526_);
v___y_2542_ = v___x_2553_;
goto v___jp_2541_;
}
else
{
lean_dec(v_fst_2536_);
lean_dec(v_fst_2529_);
v___y_2542_ = v_x_2477_;
goto v___jp_2541_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2529_);
lean_dec_ref_known(v_x_2477_, 3);
return v___x_2531_;
}
}
else
{
lean_dec_ref_known(v_x_2477_, 3);
lean_dec_ref(v_f_2476_);
return v___x_2527_;
}
}
case 10:
{
lean_object* v_data_2562_; lean_object* v_expr_2563_; lean_object* v___x_2564_; 
v_data_2562_ = lean_ctor_get(v_x_2477_, 0);
v_expr_2563_ = lean_ctor_get(v_x_2477_, 1);
lean_inc_ref(v_expr_2563_);
v___x_2564_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_expr_2563_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2587_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2587_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2587_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_fst_2569_; lean_object* v_snd_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2586_; 
v_fst_2569_ = lean_ctor_get(v_a_2565_, 0);
v_snd_2570_ = lean_ctor_get(v_a_2565_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2565_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2572_ = v_a_2565_;
v_isShared_2573_ = v_isSharedCheck_2586_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snd_2570_);
lean_inc(v_fst_2569_);
lean_dec(v_a_2565_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2586_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___y_2575_; size_t v___x_2582_; size_t v___x_2583_; uint8_t v___x_2584_; 
v___x_2582_ = lean_ptr_addr(v_expr_2563_);
v___x_2583_ = lean_ptr_addr(v_fst_2569_);
v___x_2584_ = lean_usize_dec_eq(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
lean_inc(v_data_2562_);
lean_dec_ref_known(v_x_2477_, 2);
v___x_2585_ = l_Lean_Expr_mdata___override(v_data_2562_, v_fst_2569_);
v___y_2575_ = v___x_2585_;
goto v___jp_2574_;
}
else
{
lean_dec(v_fst_2569_);
v___y_2575_ = v_x_2477_;
goto v___jp_2574_;
}
v___jp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___y_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___y_2575_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_snd_2570_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2577_);
v___x_2579_ = v___x_2567_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2477_, 2);
return v___x_2564_;
}
}
case 8:
{
lean_object* v_declName_2588_; lean_object* v_type_2589_; lean_object* v_value_2590_; lean_object* v_body_2591_; uint8_t v_nondep_2592_; lean_object* v___x_2593_; 
v_declName_2588_ = lean_ctor_get(v_x_2477_, 0);
v_type_2589_ = lean_ctor_get(v_x_2477_, 1);
v_value_2590_ = lean_ctor_get(v_x_2477_, 2);
v_body_2591_ = lean_ctor_get(v_x_2477_, 3);
v_nondep_2592_ = lean_ctor_get_uint8(v_x_2477_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2589_);
lean_inc_ref(v_f_2476_);
v___x_2593_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_type_2589_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2597_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v_fst_2595_ = lean_ctor_get(v_a_2594_, 0);
lean_inc(v_fst_2595_);
v_snd_2596_ = lean_ctor_get(v_a_2594_, 1);
lean_inc(v_snd_2596_);
lean_dec(v_a_2594_);
lean_inc_ref(v_value_2590_);
lean_inc_ref(v_f_2476_);
v___x_2597_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_value_2590_, v_snd_2596_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_fst_2599_; lean_object* v_snd_2600_; lean_object* v___x_2601_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v_fst_2599_ = lean_ctor_get(v_a_2598_, 0);
lean_inc(v_fst_2599_);
v_snd_2600_ = lean_ctor_get(v_a_2598_, 1);
lean_inc(v_snd_2600_);
lean_dec(v_a_2598_);
lean_inc_ref(v_body_2591_);
v___x_2601_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_body_2591_, v_snd_2600_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2633_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2633_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2633_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_fst_2606_; lean_object* v_snd_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2632_; 
v_fst_2606_ = lean_ctor_get(v_a_2602_, 0);
v_snd_2607_ = lean_ctor_get(v_a_2602_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2609_ = v_a_2602_;
v_isShared_2610_ = v_isSharedCheck_2632_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_snd_2607_);
lean_inc(v_fst_2606_);
lean_dec(v_a_2602_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2632_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___y_2612_; uint8_t v___y_2620_; size_t v___x_2626_; size_t v___x_2627_; uint8_t v___x_2628_; 
v___x_2626_ = lean_ptr_addr(v_type_2589_);
v___x_2627_ = lean_ptr_addr(v_fst_2595_);
v___x_2628_ = lean_usize_dec_eq(v___x_2626_, v___x_2627_);
if (v___x_2628_ == 0)
{
v___y_2620_ = v___x_2628_;
goto v___jp_2619_;
}
else
{
size_t v___x_2629_; size_t v___x_2630_; uint8_t v___x_2631_; 
v___x_2629_ = lean_ptr_addr(v_value_2590_);
v___x_2630_ = lean_ptr_addr(v_fst_2599_);
v___x_2631_ = lean_usize_dec_eq(v___x_2629_, v___x_2630_);
v___y_2620_ = v___x_2631_;
goto v___jp_2619_;
}
v___jp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___y_2612_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___y_2612_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_snd_2607_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2614_);
v___x_2616_ = v___x_2604_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
v___jp_2619_:
{
if (v___y_2620_ == 0)
{
lean_object* v___x_2621_; 
lean_inc(v_declName_2588_);
lean_dec_ref_known(v_x_2477_, 4);
v___x_2621_ = l_Lean_Expr_letE___override(v_declName_2588_, v_fst_2595_, v_fst_2599_, v_fst_2606_, v_nondep_2592_);
v___y_2612_ = v___x_2621_;
goto v___jp_2611_;
}
else
{
size_t v___x_2622_; size_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = lean_ptr_addr(v_body_2591_);
v___x_2623_ = lean_ptr_addr(v_fst_2606_);
v___x_2624_ = lean_usize_dec_eq(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_inc(v_declName_2588_);
lean_dec_ref_known(v_x_2477_, 4);
v___x_2625_ = l_Lean_Expr_letE___override(v_declName_2588_, v_fst_2595_, v_fst_2599_, v_fst_2606_, v_nondep_2592_);
v___y_2612_ = v___x_2625_;
goto v___jp_2611_;
}
else
{
lean_dec(v_fst_2606_);
lean_dec(v_fst_2599_);
lean_dec(v_fst_2595_);
v___y_2612_ = v_x_2477_;
goto v___jp_2611_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2599_);
lean_dec(v_fst_2595_);
lean_dec_ref_known(v_x_2477_, 4);
return v___x_2601_;
}
}
else
{
lean_dec(v_fst_2595_);
lean_dec_ref_known(v_x_2477_, 4);
lean_dec_ref(v_f_2476_);
return v___x_2597_;
}
}
else
{
lean_dec_ref_known(v_x_2477_, 4);
lean_dec_ref(v_f_2476_);
return v___x_2593_;
}
}
case 5:
{
lean_object* v_fn_2634_; lean_object* v_arg_2635_; lean_object* v___x_2636_; 
v_fn_2634_ = lean_ctor_get(v_x_2477_, 0);
v_arg_2635_ = lean_ctor_get(v_x_2477_, 1);
lean_inc_ref(v_fn_2634_);
lean_inc_ref(v_f_2476_);
v___x_2636_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_fn_2634_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2640_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v_fst_2638_ = lean_ctor_get(v_a_2637_, 0);
lean_inc(v_fst_2638_);
v_snd_2639_ = lean_ctor_get(v_a_2637_, 1);
lean_inc(v_snd_2639_);
lean_dec(v_a_2637_);
lean_inc_ref(v_arg_2635_);
v___x_2640_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_arg_2635_, v_snd_2639_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2668_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2668_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2668_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2667_; 
v_fst_2645_ = lean_ctor_get(v_a_2641_, 0);
v_snd_2646_ = lean_ctor_get(v_a_2641_, 1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_a_2641_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2648_ = v_a_2641_;
v_isShared_2649_ = v_isSharedCheck_2667_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_snd_2646_);
lean_inc(v_fst_2645_);
lean_dec(v_a_2641_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2667_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___y_2651_; uint8_t v___y_2659_; size_t v___x_2661_; size_t v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = lean_ptr_addr(v_fn_2634_);
v___x_2662_ = lean_ptr_addr(v_fst_2638_);
v___x_2663_ = lean_usize_dec_eq(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
v___y_2659_ = v___x_2663_;
goto v___jp_2658_;
}
else
{
size_t v___x_2664_; size_t v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = lean_ptr_addr(v_arg_2635_);
v___x_2665_ = lean_ptr_addr(v_fst_2645_);
v___x_2666_ = lean_usize_dec_eq(v___x_2664_, v___x_2665_);
v___y_2659_ = v___x_2666_;
goto v___jp_2658_;
}
v___jp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___y_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___y_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_snd_2646_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2653_);
v___x_2655_ = v___x_2643_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
v___jp_2658_:
{
if (v___y_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref_known(v_x_2477_, 2);
v___x_2660_ = l_Lean_Expr_app___override(v_fst_2638_, v_fst_2645_);
v___y_2651_ = v___x_2660_;
goto v___jp_2650_;
}
else
{
lean_dec(v_fst_2645_);
lean_dec(v_fst_2638_);
v___y_2651_ = v_x_2477_;
goto v___jp_2650_;
}
}
}
}
}
else
{
lean_dec(v_fst_2638_);
lean_dec_ref_known(v_x_2477_, 2);
return v___x_2640_;
}
}
else
{
lean_dec_ref_known(v_x_2477_, 2);
lean_dec_ref(v_f_2476_);
return v___x_2636_;
}
}
case 11:
{
lean_object* v_typeName_2669_; lean_object* v_idx_2670_; lean_object* v_struct_2671_; lean_object* v___x_2672_; 
v_typeName_2669_ = lean_ctor_get(v_x_2477_, 0);
v_idx_2670_ = lean_ctor_get(v_x_2477_, 1);
v_struct_2671_ = lean_ctor_get(v_x_2477_, 2);
lean_inc_ref(v_struct_2671_);
v___x_2672_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2476_, v_struct_2671_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2695_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2695_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2695_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2694_; 
v_fst_2677_ = lean_ctor_get(v_a_2673_, 0);
v_snd_2678_ = lean_ctor_get(v_a_2673_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2673_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2680_ = v_a_2673_;
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_snd_2678_);
lean_inc(v_fst_2677_);
lean_dec(v_a_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___y_2683_; size_t v___x_2690_; size_t v___x_2691_; uint8_t v___x_2692_; 
v___x_2690_ = lean_ptr_addr(v_struct_2671_);
v___x_2691_ = lean_ptr_addr(v_fst_2677_);
v___x_2692_ = lean_usize_dec_eq(v___x_2690_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_inc(v_idx_2670_);
lean_inc(v_typeName_2669_);
lean_dec_ref_known(v_x_2477_, 3);
v___x_2693_ = l_Lean_Expr_proj___override(v_typeName_2669_, v_idx_2670_, v_fst_2677_);
v___y_2683_ = v___x_2693_;
goto v___jp_2682_;
}
else
{
lean_dec(v_fst_2677_);
v___y_2683_ = v_x_2477_;
goto v___jp_2682_;
}
v___jp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___y_2683_);
v___x_2685_ = v___x_2680_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___y_2683_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_snd_2678_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2685_);
v___x_2687_ = v___x_2675_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2477_, 3);
return v___x_2672_;
}
}
default: 
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec_ref(v_f_2476_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_x_2477_);
lean_ctor_set(v___x_2696_, 1, v___y_2478_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2698_, lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2698_, v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2707_, lean_object* v_init_2708_, lean_object* v_e_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2707_, v_e_2709_, v_init_2708_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_snd_2720_; lean_object* v___x_2722_; 
v_snd_2720_ = lean_ctor_get(v_a_2716_, 1);
lean_inc(v_snd_2720_);
lean_dec(v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_snd_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_snd_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2715_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2715_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2733_, lean_object* v_init_2734_, lean_object* v_e_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2733_, v_init_2734_, v_e_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2744_, lean_object* v_as_2745_, size_t v_i_2746_, size_t v_stop_2747_, lean_object* v_b_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_a_2755_; uint8_t v___x_2759_; 
v___x_2759_ = lean_usize_dec_eq(v_i_2746_, v_stop_2747_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_array_uget_borrowed(v_as_2745_, v_i_2746_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___x_2760_);
v___x_2761_ = lean_infer_type(v___x_2760_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
lean_inc_ref(v_op_2744_);
v___x_2763_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2744_, v_a_2762_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l_Array_append___redArg(v_b_2748_, v_a_2764_);
lean_dec(v_a_2764_);
v_a_2755_ = v___x_2765_;
goto v___jp_2754_;
}
else
{
lean_dec_ref(v_b_2748_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2763_, 1);
v_a_2755_ = v_a_2766_;
goto v___jp_2754_;
}
else
{
lean_dec_ref(v_op_2744_);
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v_b_2748_);
lean_dec_ref(v_op_2744_);
v_a_2767_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2761_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2761_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v___x_2775_; 
lean_dec_ref(v_op_2744_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_b_2748_);
return v___x_2775_;
}
v___jp_2754_:
{
size_t v___x_2756_; size_t v___x_2757_; 
v___x_2756_ = ((size_t)1ULL);
v___x_2757_ = lean_usize_add(v_i_2746_, v___x_2756_);
v_i_2746_ = v___x_2757_;
v_b_2748_ = v_a_2755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2776_, lean_object* v_args_2777_, lean_object* v_body_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
lean_inc_ref(v_op_2776_);
v___x_2784_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2776_, v_body_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2806_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2806_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2806_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2789_ = l_Array_reverse___redArg(v_a_2785_);
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_array_get_size(v_args_2777_);
v___x_2792_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2794_; 
lean_dec_ref(v_op_2776_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2794_ = v___x_2787_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
else
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_nat_dec_le(v___x_2791_, v___x_2791_);
if (v___x_2796_ == 0)
{
if (v___x_2792_ == 0)
{
lean_object* v___x_2798_; 
lean_dec_ref(v_op_2776_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2798_ = v___x_2787_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2789_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
else
{
size_t v___x_2800_; size_t v___x_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2787_);
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = lean_usize_of_nat(v___x_2791_);
v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2776_, v_args_2777_, v___x_2800_, v___x_2801_, v___x_2789_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2802_;
}
}
else
{
size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
lean_del_object(v___x_2787_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = lean_usize_of_nat(v___x_2791_);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2776_, v_args_2777_, v___x_2803_, v___x_2804_, v___x_2789_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2805_;
}
}
}
}
else
{
lean_dec_ref(v_op_2776_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2807_, lean_object* v_args_2808_, lean_object* v_body_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2807_, v_args_2808_, v_body_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec_ref(v_args_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2816_, lean_object* v_a_2817_, lean_object* v_f_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2816_, v_a_2817_, v_f_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2825_, lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_){
_start:
{
switch(lean_obj_tag(v_e_2826_))
{
case 0:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref_known(v_e_2826_, 1);
lean_dec_ref(v_op_2825_);
v___x_2832_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
case 7:
{
lean_object* v___f_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; 
v___f_2834_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2834_, 0, v_op_2825_);
v___x_2835_ = 0;
v___x_2836_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2826_, v___f_2834_, v___x_2835_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
return v___x_2836_;
}
case 6:
{
lean_object* v___f_2837_; uint8_t v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; 
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2837_, 0, v_op_2825_);
v___x_2838_ = 0;
v___x_2839_ = 1;
v___x_2840_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2826_, v___f_2837_, v___x_2838_, v___x_2839_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
return v___x_2840_;
}
case 8:
{
lean_object* v___f_2841_; uint8_t v___x_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; 
v___f_2841_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2841_, 0, v_op_2825_);
v___x_2842_ = 0;
v___x_2843_ = 1;
v___x_2844_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2826_, v___f_2841_, v___x_2842_, v___x_2843_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
return v___x_2844_;
}
default: 
{
lean_object* v___x_2845_; 
lean_inc_ref(v_op_2825_);
lean_inc(v_a_2830_);
lean_inc_ref(v_a_2829_);
lean_inc(v_a_2828_);
lean_inc_ref(v_a_2827_);
lean_inc_ref(v_e_2826_);
v___x_2845_ = lean_apply_6(v_op_2825_, v_e_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, lean_box(0));
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2847_, 0, v_op_2825_);
v___x_2848_ = l_Array_reverse___redArg(v_a_2846_);
v___x_2849_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2847_, v___x_2848_, v_e_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
return v___x_2849_;
}
else
{
lean_dec_ref(v_e_2826_);
lean_dec_ref(v_op_2825_);
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2850_, lean_object* v_a_2851_, lean_object* v_f_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2850_, v_f_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2867_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = l_Array_append___redArg(v_a_2851_, v_a_2859_);
lean_dec(v_a_2859_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2863_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
else
{
lean_dec_ref(v_a_2851_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2868_, lean_object* v_as_2869_, lean_object* v_i_2870_, lean_object* v_stop_2871_, lean_object* v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
size_t v_i_boxed_2878_; size_t v_stop_boxed_2879_; lean_object* v_res_2880_; 
v_i_boxed_2878_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_stop_boxed_2879_ = lean_unbox_usize(v_stop_2871_);
lean_dec(v_stop_2871_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2868_, v_as_2869_, v_i_boxed_2878_, v_stop_boxed_2879_, v_b_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_as_2869_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2881_, lean_object* v_e_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2881_, v_e_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2889_, lean_object* v_op_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2890_, v_e_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_op_2899_, lean_object* v_e_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2898_, v_op_2899_, v_e_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2907_, lean_object* v_op_2908_, lean_object* v_as_2909_, size_t v_i_2910_, size_t v_stop_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2908_, v_as_2909_, v_i_2910_, v_stop_2911_, v_b_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2919_, lean_object* v_op_2920_, lean_object* v_as_2921_, lean_object* v_i_2922_, lean_object* v_stop_2923_, lean_object* v_b_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
size_t v_i_boxed_2930_; size_t v_stop_boxed_2931_; lean_object* v_res_2932_; 
v_i_boxed_2930_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_stop_boxed_2931_ = lean_unbox_usize(v_stop_2923_);
lean_dec(v_stop_2923_);
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2919_, v_op_2920_, v_as_2921_, v_i_boxed_2930_, v_stop_boxed_2931_, v_b_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_as_2921_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2933_, lean_object* v_f_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2934_, v_x_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_f_2944_, lean_object* v_x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2943_, v_f_2944_, v_x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2953_, lean_object* v_f_2954_, lean_object* v_init_2955_, lean_object* v_e_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2954_, v_init_2955_, v_e_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2963_, lean_object* v_f_2964_, lean_object* v_init_2965_, lean_object* v_e_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2963_, v_f_2964_, v_init_2965_, v_e_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_bs_2975_){
_start:
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
if (v___x_2976_ == 0)
{
return v_bs_2975_;
}
else
{
lean_object* v_v_2977_; lean_object* v_fst_2978_; lean_object* v_snd_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2993_; 
v_v_2977_ = lean_array_uget(v_bs_2975_, v_i_2974_);
v_fst_2978_ = lean_ctor_get(v_v_2977_, 0);
v_snd_2979_ = lean_ctor_get(v_v_2977_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_v_2977_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2981_ = v_v_2977_;
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_snd_2979_);
lean_inc(v_fst_2978_);
lean_dec(v_v_2977_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v_bs_x27_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
v_bs_x27_2984_ = lean_array_uset(v_bs_2975_, v_i_2974_, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_fst_2978_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2985_);
v___x_2987_ = v___x_2981_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_snd_2979_);
v___x_2987_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
size_t v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((size_t)1ULL);
v___x_2989_ = lean_usize_add(v_i_2974_, v___x_2988_);
v___x_2990_ = lean_array_uset(v_bs_x27_2984_, v_i_2974_, v___x_2987_);
v_i_2974_ = v___x_2989_;
v_bs_2975_ = v___x_2990_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2994_, lean_object* v_i_2995_, lean_object* v_bs_2996_){
_start:
{
size_t v_sz_boxed_2997_; size_t v_i_boxed_2998_; lean_object* v_res_2999_; 
v_sz_boxed_2997_ = lean_unbox_usize(v_sz_2994_);
lean_dec(v_sz_2994_);
v_i_boxed_2998_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2997_, v_i_boxed_2998_, v_bs_2996_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3000_, lean_object* v_j_3001_){
_start:
{
lean_object* v_zero_3002_; uint8_t v_isZero_3003_; 
v_zero_3002_ = lean_unsigned_to_nat(0u);
v_isZero_3003_ = lean_nat_dec_eq(v_j_3001_, v_zero_3002_);
if (v_isZero_3003_ == 1)
{
lean_dec(v_j_3001_);
return v_xs_3000_;
}
else
{
lean_object* v___x_3004_; lean_object* v_snd_3005_; lean_object* v_snd_3006_; lean_object* v_one_3007_; lean_object* v_n_3008_; lean_object* v___x_3009_; lean_object* v_snd_3010_; lean_object* v_snd_3011_; uint8_t v___x_3012_; 
v___x_3004_ = lean_array_fget_borrowed(v_xs_3000_, v_j_3001_);
v_snd_3005_ = lean_ctor_get(v___x_3004_, 1);
v_snd_3006_ = lean_ctor_get(v_snd_3005_, 1);
v_one_3007_ = lean_unsigned_to_nat(1u);
v_n_3008_ = lean_nat_sub(v_j_3001_, v_one_3007_);
v___x_3009_ = lean_array_fget_borrowed(v_xs_3000_, v_n_3008_);
v_snd_3010_ = lean_ctor_get(v___x_3009_, 1);
v_snd_3011_ = lean_ctor_get(v_snd_3010_, 1);
v___x_3012_ = lean_nat_dec_lt(v_snd_3011_, v_snd_3006_);
if (v___x_3012_ == 0)
{
lean_dec(v_n_3008_);
lean_dec(v_j_3001_);
return v_xs_3000_;
}
else
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_array_fswap(v_xs_3000_, v_j_3001_, v_n_3008_);
lean_dec(v_j_3001_);
v_xs_3000_ = v___x_3013_;
v_j_3001_ = v_n_3008_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3015_, lean_object* v_i_3016_, lean_object* v_fuel_3017_){
_start:
{
lean_object* v_zero_3018_; uint8_t v_isZero_3019_; 
v_zero_3018_ = lean_unsigned_to_nat(0u);
v_isZero_3019_ = lean_nat_dec_eq(v_fuel_3017_, v_zero_3018_);
if (v_isZero_3019_ == 1)
{
lean_dec(v_fuel_3017_);
lean_dec(v_i_3016_);
return v_xs_3015_;
}
else
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = lean_array_get_size(v_xs_3015_);
v___x_3021_ = lean_nat_dec_lt(v_i_3016_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_dec(v_fuel_3017_);
lean_dec(v_i_3016_);
return v_xs_3015_;
}
else
{
lean_object* v_one_3022_; lean_object* v_n_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_one_3022_ = lean_unsigned_to_nat(1u);
v_n_3023_ = lean_nat_sub(v_fuel_3017_, v_one_3022_);
lean_dec(v_fuel_3017_);
lean_inc(v_i_3016_);
v___x_3024_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3015_, v_i_3016_);
v___x_3025_ = lean_nat_add(v_i_3016_, v_one_3022_);
lean_dec(v_i_3016_);
v_xs_3015_ = v___x_3024_;
v_i_3016_ = v___x_3025_;
v_fuel_3017_ = v_n_3023_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3027_, size_t v_i_3028_, lean_object* v_bs_3029_){
_start:
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_usize_dec_lt(v_i_3028_, v_sz_3027_);
if (v___x_3030_ == 0)
{
return v_bs_3029_;
}
else
{
lean_object* v_v_3031_; lean_object* v_fst_3032_; lean_object* v_snd_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3047_; 
v_v_3031_ = lean_array_uget(v_bs_3029_, v_i_3028_);
v_fst_3032_ = lean_ctor_get(v_v_3031_, 0);
v_snd_3033_ = lean_ctor_get(v_v_3031_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_v_3031_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3035_ = v_v_3031_;
v_isShared_3036_ = v_isSharedCheck_3047_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_snd_3033_);
lean_inc(v_fst_3032_);
lean_dec(v_v_3031_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3047_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v_bs_x27_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v_bs_x27_3038_ = lean_array_uset(v_bs_3029_, v_i_3028_, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_fst_3032_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3039_);
v___x_3041_ = v___x_3035_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_snd_3033_);
v___x_3041_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
size_t v___x_3042_; size_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = ((size_t)1ULL);
v___x_3043_ = lean_usize_add(v_i_3028_, v___x_3042_);
v___x_3044_ = lean_array_uset(v_bs_x27_3038_, v_i_3028_, v___x_3041_);
v_i_3028_ = v___x_3043_;
v_bs_3029_ = v___x_3044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_bs_3050_){
_start:
{
size_t v_sz_boxed_3051_; size_t v_i_boxed_3052_; lean_object* v_res_3053_; 
v_sz_boxed_3051_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3051_, v_i_boxed_3052_, v_bs_3050_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3054_, lean_object* v_as_3055_, size_t v_sz_3056_, size_t v_i_3057_, lean_object* v_b_3058_){
_start:
{
lean_object* v_a_3061_; uint8_t v___x_3065_; 
v___x_3065_ = lean_usize_dec_lt(v_i_3057_, v_sz_3056_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_b_3058_);
return v___x_3066_;
}
else
{
lean_object* v_a_3067_; lean_object* v_snd_3068_; lean_object* v_snd_3069_; lean_object* v_fst_3070_; lean_object* v_fst_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3121_; 
v_a_3067_ = lean_array_uget(v_as_3055_, v_i_3057_);
v_snd_3068_ = lean_ctor_get(v_a_3067_, 1);
lean_inc(v_snd_3068_);
v_snd_3069_ = lean_ctor_get(v_b_3058_, 1);
lean_inc(v_snd_3069_);
v_fst_3070_ = lean_ctor_get(v_a_3067_, 0);
v_fst_3071_ = lean_ctor_get(v_snd_3068_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_snd_3068_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v_snd_3068_, 1);
lean_dec(v_unused_3122_);
v___x_3073_ = v_snd_3068_;
v_isShared_3074_ = v_isSharedCheck_3121_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_fst_3071_);
lean_dec(v_snd_3068_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3121_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_fst_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3119_; 
v_fst_3075_ = lean_ctor_get(v_b_3058_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_b_3058_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v_b_3058_, 1);
lean_dec(v_unused_3120_);
v___x_3077_ = v_b_3058_;
v_isShared_3078_ = v_isSharedCheck_3119_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_fst_3075_);
lean_dec(v_b_3058_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3119_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_fst_3079_; lean_object* v_snd_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3118_; 
v_fst_3079_ = lean_ctor_get(v_snd_3069_, 0);
v_snd_3080_ = lean_ctor_get(v_snd_3069_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_snd_3069_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3082_ = v_snd_3069_;
v_isShared_3083_ = v_isSharedCheck_3118_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_snd_3080_);
lean_inc(v_fst_3079_);
lean_dec(v_snd_3069_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3118_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
uint8_t v___x_3096_; 
v___x_3096_ = l_Lean_NameSet_contains(v_forbidden_3054_, v_fst_3070_);
if (v___x_3096_ == 0)
{
uint8_t v___x_3097_; 
lean_inc(v_fst_3070_);
v___x_3097_ = lean_unbox(v_fst_3071_);
lean_dec(v_fst_3071_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
v___x_3098_ = l_Lean_NameSet_contains(v_fst_3075_, v_fst_3070_);
if (v___x_3098_ == 0)
{
if (v___x_3065_ == 0)
{
lean_dec(v_fst_3070_);
lean_dec(v_a_3067_);
goto v___jp_3091_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_del_object(v___x_3073_);
v___x_3099_ = lean_array_push(v_snd_3080_, v_a_3067_);
v___x_3100_ = l_Lean_NameSet_insert(v_fst_3075_, v_fst_3070_);
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v_fst_3079_);
lean_ctor_set(v___x_3101_, 1, v___x_3099_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v_a_3061_ = v___x_3102_;
goto v___jp_3060_;
}
}
else
{
lean_dec(v_fst_3070_);
lean_dec(v_a_3067_);
goto v___jp_3091_;
}
}
else
{
uint8_t v___x_3103_; 
lean_del_object(v___x_3073_);
v___x_3103_ = l_Lean_NameSet_contains(v_fst_3079_, v_fst_3070_);
if (v___x_3103_ == 0)
{
if (v___x_3065_ == 0)
{
lean_dec(v_fst_3070_);
lean_dec(v_a_3067_);
goto v___jp_3084_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
v___x_3104_ = lean_array_push(v_snd_3080_, v_a_3067_);
v___x_3105_ = l_Lean_NameSet_insert(v_fst_3079_, v_fst_3070_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_fst_3075_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v_a_3061_ = v___x_3107_;
goto v___jp_3060_;
}
}
else
{
lean_dec(v_fst_3070_);
lean_dec(v_a_3067_);
goto v___jp_3084_;
}
}
}
else
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_dec(v_fst_3071_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_3067_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; lean_object* v_unused_3117_; 
v_unused_3116_ = lean_ctor_get(v_a_3067_, 1);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_a_3067_, 0);
lean_dec(v_unused_3117_);
v___x_3109_ = v_a_3067_;
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v_a_3067_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v_snd_3080_);
lean_ctor_set(v___x_3109_, 0, v_fst_3079_);
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_snd_3080_);
v___x_3112_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_fst_3075_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v_a_3061_ = v___x_3113_;
goto v___jp_3060_;
}
}
}
v___jp_3084_:
{
lean_object* v___x_3086_; 
if (v_isShared_3083_ == 0)
{
v___x_3086_ = v___x_3082_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_snd_3080_);
v___x_3086_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3086_);
v___x_3088_ = v___x_3077_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_fst_3075_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
v_a_3061_ = v___x_3088_;
goto v___jp_3060_;
}
}
}
v___jp_3091_:
{
lean_object* v___x_3093_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v_snd_3080_);
lean_ctor_set(v___x_3073_, 0, v_fst_3079_);
v___x_3093_ = v___x_3073_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_snd_3080_);
v___x_3093_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_fst_3075_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v_a_3061_ = v___x_3094_;
goto v___jp_3060_;
}
}
}
}
}
}
v___jp_3060_:
{
size_t v___x_3062_; size_t v___x_3063_; 
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_add(v_i_3057_, v___x_3062_);
v_i_3057_ = v___x_3063_;
v_b_3058_ = v_a_3061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3123_, lean_object* v_as_3124_, lean_object* v_sz_3125_, lean_object* v_i_3126_, lean_object* v_b_3127_, lean_object* v___y_3128_){
_start:
{
size_t v_sz_boxed_3129_; size_t v_i_boxed_3130_; lean_object* v_res_3131_; 
v_sz_boxed_3129_ = lean_unbox_usize(v_sz_3125_);
lean_dec(v_sz_3125_);
v_i_boxed_3130_ = lean_unbox_usize(v_i_3126_);
lean_dec(v_i_3126_);
v_res_3131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3123_, v_as_3124_, v_sz_boxed_3129_, v_i_boxed_3130_, v_b_3127_);
lean_dec_ref(v_as_3124_);
lean_dec(v_forbidden_3123_);
return v_res_3131_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3136_ = l_Lean_MessageData_ofFormat(v___x_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_box(1);
v___x_3138_ = l_Lean_MessageData_ofFormat(v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
if (lean_obj_tag(v_a_3141_) == 0)
{
lean_object* v___x_3143_; 
v___x_3143_ = l_List_reverse___redArg(v_a_3142_);
return v___x_3143_;
}
else
{
lean_object* v_head_3144_; lean_object* v_snd_3145_; lean_object* v_tail_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3191_; 
v_head_3144_ = lean_ctor_get(v_a_3141_, 0);
lean_inc(v_head_3144_);
v_snd_3145_ = lean_ctor_get(v_head_3144_, 1);
lean_inc(v_snd_3145_);
v_tail_3146_ = lean_ctor_get(v_a_3141_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_3141_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v_a_3141_, 0);
lean_dec(v_unused_3192_);
v___x_3148_ = v_a_3141_;
v_isShared_3149_ = v_isSharedCheck_3191_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_tail_3146_);
lean_dec(v_a_3141_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3191_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3189_; 
v_fst_3150_ = lean_ctor_get(v_head_3144_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_head_3144_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v_head_3144_, 1);
lean_dec(v_unused_3190_);
v___x_3152_ = v_head_3144_;
v_isShared_3153_ = v_isSharedCheck_3189_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_fst_3150_);
lean_dec(v_head_3144_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3189_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_fst_3154_; lean_object* v_snd_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3188_; 
v_fst_3154_ = lean_ctor_get(v_snd_3145_, 0);
v_snd_3155_ = lean_ctor_get(v_snd_3145_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_snd_3145_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3157_ = v_snd_3145_;
v_isShared_3158_ = v_isSharedCheck_3188_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_snd_3155_);
lean_inc(v_fst_3154_);
lean_dec(v_snd_3145_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3188_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3159_ = l_Lean_MessageData_ofName(v_fst_3150_);
v___x_3160_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 7);
lean_ctor_set(v___x_3157_, 1, v___x_3160_);
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 7);
lean_ctor_set(v___x_3152_, 1, v___x_3163_);
lean_ctor_set(v___x_3152_, 0, v___x_3162_);
v___x_3165_ = v___x_3152_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___y_3167_; uint8_t v___x_3183_; 
v___x_3183_ = lean_unbox(v_fst_3154_);
lean_dec(v_fst_3154_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
v___x_3184_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3167_ = v___x_3184_;
goto v___jp_3166_;
}
else
{
lean_object* v___x_3185_; 
v___x_3185_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3167_ = v___x_3185_;
goto v___jp_3166_;
}
v___jp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_inc_ref(v___y_3167_);
v___x_3168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3167_);
v___x_3169_ = l_Lean_MessageData_ofFormat(v___x_3168_);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3160_);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3163_);
v___x_3172_ = l_Nat_reprFast(v_snd_3155_);
v___x_3173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
v___x_3174_ = l_Lean_MessageData_ofFormat(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3171_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_MessageData_paren(v___x_3175_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3165_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_MessageData_paren(v___x_3177_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v_a_3142_);
lean_ctor_set(v___x_3148_, 0, v___x_3178_);
v___x_3180_ = v___x_3148_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_a_3142_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
v_a_3141_ = v_tail_3146_;
v_a_3142_ = v___x_3180_;
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
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3196_ = l_Lean_NameSet_empty;
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3199_ = l_Lean_NameSet_empty;
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3198_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3202_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3203_ = l_Lean_Name_append(v___x_3202_, v___x_3201_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3207_, lean_object* v_moduleRef_3208_, lean_object* v_target_3209_, lean_object* v_forbidden_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3216_, 0, v_moduleRef_3208_);
v___x_3217_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3216_, v_target_3209_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; size_t v_sz_3223_; size_t v___x_3224_; lean_object* v___x_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_array_get_size(v_a_3218_);
v___x_3221_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3218_, v___x_3219_, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3223_ = lean_array_size(v___x_3221_);
v___x_3224_ = ((size_t)0ULL);
v___x_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3210_, v___x_3221_, v_sz_3223_, v___x_3224_, v___x_3222_);
lean_dec_ref(v___x_3221_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3269_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3269_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3269_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_snd_3230_; lean_object* v_snd_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3267_; 
v_snd_3230_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3226_);
v_snd_3231_ = lean_ctor_get(v_snd_3230_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_snd_3230_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_snd_3230_, 0);
lean_dec(v_unused_3268_);
v___x_3233_ = v_snd_3230_;
v_isShared_3234_ = v_isSharedCheck_3267_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_snd_3231_);
lean_dec(v_snd_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3267_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_options_3244_; uint8_t v_hasTrace_3245_; 
v_options_3244_ = lean_ctor_get(v_a_3213_, 2);
v_hasTrace_3245_ = lean_ctor_get_uint8(v_options_3244_, sizeof(void*)*1);
if (v_hasTrace_3245_ == 0)
{
lean_del_object(v___x_3233_);
goto v___jp_3235_;
}
else
{
lean_object* v_inheritedTraceOptions_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_inheritedTraceOptions_3246_ = lean_ctor_get(v_a_3213_, 13);
v___x_3247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3248_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3246_, v_options_3244_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_del_object(v___x_3233_);
goto v___jp_3235_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3250_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3231_);
v___x_3251_ = lean_array_to_list(v_snd_3231_);
v___x_3252_ = lean_box(0);
v___x_3253_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3251_, v___x_3252_);
v___x_3254_ = l_Lean_MessageData_ofList(v___x_3253_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 7);
lean_ctor_set(v___x_3233_, 1, v___x_3254_);
lean_ctor_set(v___x_3233_, 0, v___x_3250_);
v___x_3256_ = v___x_3233_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3247_, v___x_3256_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref_known(v___x_3257_, 1);
goto v___jp_3235_;
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_snd_3231_);
lean_del_object(v___x_3228_);
lean_dec_ref(v_hyps_3207_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
}
v___jp_3235_:
{
size_t v_sz_3236_; lean_object* v___x_3237_; size_t v_sz_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v_sz_3236_ = lean_array_size(v_hyps_3207_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3236_, v___x_3224_, v_hyps_3207_);
v_sz_3238_ = lean_array_size(v_snd_3231_);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3238_, v___x_3224_, v_snd_3231_);
v___x_3240_ = l_Array_append___redArg(v___x_3237_, v___x_3239_);
lean_dec_ref(v___x_3239_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3240_);
v___x_3242_ = v___x_3228_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_hyps_3207_);
v_a_3270_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3225_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3225_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_hyps_3207_);
v_a_3278_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3217_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3217_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3286_, lean_object* v_moduleRef_3287_, lean_object* v_target_3288_, lean_object* v_forbidden_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3286_, v_moduleRef_3287_, v_target_3288_, v_forbidden_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_forbidden_3289_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3296_, lean_object* v_as_3297_, size_t v_sz_3298_, size_t v_i_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3296_, v_as_3297_, v_sz_3298_, v_i_3299_, v_b_3300_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3307_, lean_object* v_as_3308_, lean_object* v_sz_3309_, lean_object* v_i_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
size_t v_sz_boxed_3317_; size_t v_i_boxed_3318_; lean_object* v_res_3319_; 
v_sz_boxed_3317_ = lean_unbox_usize(v_sz_3309_);
lean_dec(v_sz_3309_);
v_i_boxed_3318_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3307_, v_as_3308_, v_sz_boxed_3317_, v_i_boxed_3318_, v_b_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_as_3308_);
lean_dec(v_forbidden_3307_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3320_, lean_object* v_j_3321_, lean_object* v_h_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3320_, v_j_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3324_){
_start:
{
uint8_t v_rfl_x3f_3325_; 
v_rfl_x3f_3325_ = lean_ctor_get_uint8(v_r_3324_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3325_ == 0)
{
lean_object* v_result_3326_; lean_object* v_eNew_3327_; lean_object* v___x_3328_; 
v_result_3326_ = lean_ctor_get(v_r_3324_, 2);
v_eNew_3327_ = lean_ctor_get(v_result_3326_, 0);
lean_inc_ref(v_eNew_3327_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_eNew_3327_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_box(0);
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3330_);
lean_dec_ref(v_r_3330_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
v___x_3342_ = lean_apply_9(v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, lean_box(0));
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___f_3365_; lean_object* v___x_3366_; 
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3365_, 0, v_x_3355_);
lean_closure_set(v___f_3365_, 1, v___y_3356_);
lean_closure_set(v___f_3365_, 2, v___y_3357_);
lean_closure_set(v___f_3365_, 3, v___y_3358_);
lean_closure_set(v___f_3365_, 4, v___y_3359_);
v___x_3366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3354_, v___f_3365_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3366_) == 0)
{
return v___x_3366_;
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3375_, lean_object* v_x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3375_, v_x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3387_, lean_object* v_mctx_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3388_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3400_, lean_object* v_mctx_3401_, lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3400_, v_mctx_3401_, v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3413_, uint8_t v_symm_3414_, lean_object* v_r_3415_, lean_object* v_ref_3416_, lean_object* v_checkState_x3f_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3419_, v___y_3421_, v___y_3423_, v___y_3425_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v_ref_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___y_3439_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v_ref_3429_ = lean_ctor_get(v___y_3424_, 5);
v___x_3430_ = lean_box(v_symm_3414_);
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v_expr_3413_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_box(0);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3415_);
v___x_3435_ = l_Option_toLOption___redArg(v___x_3434_);
v___x_3436_ = lean_box(0);
lean_inc(v_ref_3429_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_ref_3429_);
if (lean_obj_tag(v_checkState_x3f_3417_) == 0)
{
v___y_3439_ = v_a_3428_;
goto v___jp_3438_;
}
else
{
lean_object* v_val_3442_; 
lean_dec(v_a_3428_);
v_val_3442_ = lean_ctor_get(v_checkState_x3f_3417_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v_checkState_x3f_3417_, 1);
v___y_3439_ = v_val_3442_;
goto v___jp_3438_;
}
v___jp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___y_3439_);
v___x_3441_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3416_, v___x_3433_, v___x_3435_, v___x_3436_, v___x_3437_, v___x_3440_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3441_;
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_checkState_x3f_3417_);
lean_dec(v_ref_3416_);
lean_dec_ref(v_expr_3413_);
v_a_3443_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3427_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3427_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3451_, lean_object* v_symm_3452_, lean_object* v_r_3453_, lean_object* v_ref_3454_, lean_object* v_checkState_x3f_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v_symm_boxed_3465_; lean_object* v_res_3466_; 
v_symm_boxed_3465_ = lean_unbox(v_symm_3452_);
v_res_3466_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3451_, v_symm_boxed_3465_, v_r_3453_, v_ref_3454_, v_checkState_x3f_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_r_3453_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3467_, lean_object* v_r_3468_, lean_object* v_checkState_x3f_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_expr_3479_; uint8_t v_symm_3480_; lean_object* v_mctx_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; 
v_expr_3479_ = lean_ctor_get(v_r_3468_, 0);
lean_inc_ref(v_expr_3479_);
v_symm_3480_ = lean_ctor_get_uint8(v_r_3468_, sizeof(void*)*4);
v_mctx_3481_ = lean_ctor_get(v_r_3468_, 3);
lean_inc_ref(v_mctx_3481_);
v___x_3482_ = lean_box(v_symm_3480_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3483_, 0, v_expr_3479_);
lean_closure_set(v___f_3483_, 1, v___x_3482_);
lean_closure_set(v___f_3483_, 2, v_r_3468_);
lean_closure_set(v___f_3483_, 3, v_ref_3467_);
lean_closure_set(v___f_3483_, 4, v_checkState_x3f_3469_);
v___x_3484_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3481_, v___f_3483_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3485_, lean_object* v_r_3486_, lean_object* v_checkState_x3f_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3485_, v_r_3486_, v_checkState_x3f_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3498_, lean_object* v_b_3499_, lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_dec(v_b_3499_);
lean_dec_ref(v_a_3498_);
return v_x_3500_;
}
else
{
lean_object* v_key_3501_; lean_object* v_value_3502_; lean_object* v_tail_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3515_; 
v_key_3501_ = lean_ctor_get(v_x_3500_, 0);
v_value_3502_ = lean_ctor_get(v_x_3500_, 1);
v_tail_3503_ = lean_ctor_get(v_x_3500_, 2);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_x_3500_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3505_ = v_x_3500_;
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_tail_3503_);
lean_inc(v_value_3502_);
lean_inc(v_key_3501_);
lean_dec(v_x_3500_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_string_dec_eq(v_key_3501_, v_a_3498_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3498_, v_b_3499_, v_tail_3503_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 2, v___x_3508_);
v___x_3510_ = v___x_3505_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_key_3501_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_value_3502_);
lean_ctor_set(v_reuseFailAlloc_3511_, 2, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_value_3502_);
lean_dec(v_key_3501_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v_b_3499_);
lean_ctor_set(v___x_3505_, 0, v_a_3498_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3498_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_b_3499_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v_tail_3503_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
if (lean_obj_tag(v_x_3517_) == 0)
{
return v_x_3516_;
}
else
{
lean_object* v_key_3518_; lean_object* v_value_3519_; lean_object* v_tail_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3543_; 
v_key_3518_ = lean_ctor_get(v_x_3517_, 0);
v_value_3519_ = lean_ctor_get(v_x_3517_, 1);
v_tail_3520_ = lean_ctor_get(v_x_3517_, 2);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_x_3517_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3522_ = v_x_3517_;
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_tail_3520_);
lean_inc(v_value_3519_);
lean_inc(v_key_3518_);
lean_dec(v_x_3517_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; uint64_t v___x_3525_; uint64_t v___x_3526_; uint64_t v___x_3527_; uint64_t v_fold_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; size_t v___x_3532_; size_t v___x_3533_; size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3524_ = lean_array_get_size(v_x_3516_);
v___x_3525_ = lean_string_hash(v_key_3518_);
v___x_3526_ = 32ULL;
v___x_3527_ = lean_uint64_shift_right(v___x_3525_, v___x_3526_);
v_fold_3528_ = lean_uint64_xor(v___x_3525_, v___x_3527_);
v___x_3529_ = 16ULL;
v___x_3530_ = lean_uint64_shift_right(v_fold_3528_, v___x_3529_);
v___x_3531_ = lean_uint64_xor(v_fold_3528_, v___x_3530_);
v___x_3532_ = lean_uint64_to_usize(v___x_3531_);
v___x_3533_ = lean_usize_of_nat(v___x_3524_);
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_sub(v___x_3533_, v___x_3534_);
v___x_3536_ = lean_usize_land(v___x_3532_, v___x_3535_);
v___x_3537_ = lean_array_uget_borrowed(v_x_3516_, v___x_3536_);
lean_inc(v___x_3537_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 2, v___x_3537_);
v___x_3539_ = v___x_3522_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_key_3518_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_value_3519_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_array_uset(v_x_3516_, v___x_3536_, v___x_3539_);
v_x_3516_ = v___x_3540_;
v_x_3517_ = v_tail_3520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3544_, lean_object* v_source_3545_, lean_object* v_target_3546_){
_start:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = lean_array_get_size(v_source_3545_);
v___x_3548_ = lean_nat_dec_lt(v_i_3544_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_dec_ref(v_source_3545_);
lean_dec(v_i_3544_);
return v_target_3546_;
}
else
{
lean_object* v_es_3549_; lean_object* v___x_3550_; lean_object* v_source_3551_; lean_object* v_target_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v_es_3549_ = lean_array_fget(v_source_3545_, v_i_3544_);
v___x_3550_ = lean_box(0);
v_source_3551_ = lean_array_fset(v_source_3545_, v_i_3544_, v___x_3550_);
v_target_3552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3546_, v_es_3549_);
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_nat_add(v_i_3544_, v___x_3553_);
lean_dec(v_i_3544_);
v_i_3544_ = v___x_3554_;
v_source_3545_ = v_source_3551_;
v_target_3546_ = v_target_3552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_nbuckets_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3557_ = lean_array_get_size(v_data_3556_);
v___x_3558_ = lean_unsigned_to_nat(2u);
v_nbuckets_3559_ = lean_nat_mul(v___x_3557_, v___x_3558_);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_mk_array(v_nbuckets_3559_, v___x_3561_);
v___x_3563_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3560_, v_data_3556_, v___x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
uint8_t v___x_3566_; 
v___x_3566_ = 0;
return v___x_3566_;
}
else
{
lean_object* v_key_3567_; lean_object* v_tail_3568_; uint8_t v___x_3569_; 
v_key_3567_ = lean_ctor_get(v_x_3565_, 0);
v_tail_3568_ = lean_ctor_get(v_x_3565_, 2);
v___x_3569_ = lean_string_dec_eq(v_key_3567_, v_a_3564_);
if (v___x_3569_ == 0)
{
v_x_3565_ = v_tail_3568_;
goto _start;
}
else
{
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3571_, lean_object* v_x_3572_){
_start:
{
uint8_t v_res_3573_; lean_object* v_r_3574_; 
v_res_3573_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3571_, v_x_3572_);
lean_dec(v_x_3572_);
lean_dec_ref(v_a_3571_);
v_r_3574_ = lean_box(v_res_3573_);
return v_r_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3575_, lean_object* v_a_3576_, lean_object* v_b_3577_){
_start:
{
lean_object* v_size_3578_; lean_object* v_buckets_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3622_; 
v_size_3578_ = lean_ctor_get(v_m_3575_, 0);
v_buckets_3579_ = lean_ctor_get(v_m_3575_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_m_3575_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3581_ = v_m_3575_;
v_isShared_3582_ = v_isSharedCheck_3622_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_buckets_3579_);
lean_inc(v_size_3578_);
lean_dec(v_m_3575_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3622_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; uint64_t v___x_3584_; uint64_t v___x_3585_; uint64_t v___x_3586_; uint64_t v_fold_3587_; uint64_t v___x_3588_; uint64_t v___x_3589_; uint64_t v___x_3590_; size_t v___x_3591_; size_t v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; lean_object* v_bkt_3596_; uint8_t v___x_3597_; 
v___x_3583_ = lean_array_get_size(v_buckets_3579_);
v___x_3584_ = lean_string_hash(v_a_3576_);
v___x_3585_ = 32ULL;
v___x_3586_ = lean_uint64_shift_right(v___x_3584_, v___x_3585_);
v_fold_3587_ = lean_uint64_xor(v___x_3584_, v___x_3586_);
v___x_3588_ = 16ULL;
v___x_3589_ = lean_uint64_shift_right(v_fold_3587_, v___x_3588_);
v___x_3590_ = lean_uint64_xor(v_fold_3587_, v___x_3589_);
v___x_3591_ = lean_uint64_to_usize(v___x_3590_);
v___x_3592_ = lean_usize_of_nat(v___x_3583_);
v___x_3593_ = ((size_t)1ULL);
v___x_3594_ = lean_usize_sub(v___x_3592_, v___x_3593_);
v___x_3595_ = lean_usize_land(v___x_3591_, v___x_3594_);
v_bkt_3596_ = lean_array_uget_borrowed(v_buckets_3579_, v___x_3595_);
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3576_, v_bkt_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v_size_x27_3599_; lean_object* v___x_3600_; lean_object* v_buckets_x27_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3598_ = lean_unsigned_to_nat(1u);
v_size_x27_3599_ = lean_nat_add(v_size_3578_, v___x_3598_);
lean_dec(v_size_3578_);
lean_inc(v_bkt_3596_);
v___x_3600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3600_, 0, v_a_3576_);
lean_ctor_set(v___x_3600_, 1, v_b_3577_);
lean_ctor_set(v___x_3600_, 2, v_bkt_3596_);
v_buckets_x27_3601_ = lean_array_uset(v_buckets_3579_, v___x_3595_, v___x_3600_);
v___x_3602_ = lean_unsigned_to_nat(4u);
v___x_3603_ = lean_nat_mul(v_size_x27_3599_, v___x_3602_);
v___x_3604_ = lean_unsigned_to_nat(3u);
v___x_3605_ = lean_nat_div(v___x_3603_, v___x_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_array_get_size(v_buckets_x27_3601_);
v___x_3607_ = lean_nat_dec_le(v___x_3605_, v___x_3606_);
lean_dec(v___x_3605_);
if (v___x_3607_ == 0)
{
lean_object* v_val_3608_; lean_object* v___x_3610_; 
v_val_3608_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3601_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_val_3608_);
lean_ctor_set(v___x_3581_, 0, v_size_x27_3599_);
v___x_3610_ = v___x_3581_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_size_x27_3599_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_val_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
else
{
lean_object* v___x_3613_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_buckets_x27_3601_);
lean_ctor_set(v___x_3581_, 0, v_size_x27_3599_);
v___x_3613_ = v___x_3581_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_size_x27_3599_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_buckets_x27_3601_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v___x_3615_; lean_object* v_buckets_x27_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_inc(v_bkt_3596_);
v___x_3615_ = lean_box(0);
v_buckets_x27_3616_ = lean_array_uset(v_buckets_3579_, v___x_3595_, v___x_3615_);
v___x_3617_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3576_, v_b_3577_, v_bkt_3596_);
v___x_3618_ = lean_array_uset(v_buckets_x27_3616_, v___x_3595_, v___x_3617_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3618_);
v___x_3620_ = v___x_3581_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_size_3578_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_buckets_3625_; lean_object* v___x_3626_; uint64_t v___x_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v_fold_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v_buckets_3625_ = lean_ctor_get(v_m_3623_, 1);
v___x_3626_ = lean_array_get_size(v_buckets_3625_);
v___x_3627_ = lean_string_hash(v_a_3624_);
v___x_3628_ = 32ULL;
v___x_3629_ = lean_uint64_shift_right(v___x_3627_, v___x_3628_);
v_fold_3630_ = lean_uint64_xor(v___x_3627_, v___x_3629_);
v___x_3631_ = 16ULL;
v___x_3632_ = lean_uint64_shift_right(v_fold_3630_, v___x_3631_);
v___x_3633_ = lean_uint64_xor(v_fold_3630_, v___x_3632_);
v___x_3634_ = lean_uint64_to_usize(v___x_3633_);
v___x_3635_ = lean_usize_of_nat(v___x_3626_);
v___x_3636_ = ((size_t)1ULL);
v___x_3637_ = lean_usize_sub(v___x_3635_, v___x_3636_);
v___x_3638_ = lean_usize_land(v___x_3634_, v___x_3637_);
v___x_3639_ = lean_array_uget_borrowed(v_buckets_3625_, v___x_3638_);
v___x_3640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3624_, v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3641_, lean_object* v_a_3642_){
_start:
{
uint8_t v_res_3643_; lean_object* v_r_3644_; 
v_res_3643_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3641_, v_a_3642_);
lean_dec_ref(v_a_3642_);
lean_dec_ref(v_m_3641_);
v_r_3644_ = lean_box(v_res_3643_);
return v_r_3644_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3645_, lean_object* v_as_x27_3646_, lean_object* v_b_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
if (lean_obj_tag(v_as_x27_3646_) == 0)
{
lean_object* v___x_3653_; 
lean_dec_ref(v_cfg_3645_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_b_3647_);
return v___x_3653_;
}
else
{
lean_object* v_head_3654_; lean_object* v_snd_3655_; lean_object* v_tail_3656_; lean_object* v_fst_3657_; lean_object* v_fst_3658_; lean_object* v_snd_3659_; lean_object* v___x_3660_; 
v_head_3654_ = lean_ctor_get(v_as_x27_3646_, 0);
v_snd_3655_ = lean_ctor_get(v_head_3654_, 1);
v_tail_3656_ = lean_ctor_get(v_as_x27_3646_, 1);
v_fst_3657_ = lean_ctor_get(v_head_3654_, 0);
v_fst_3658_ = lean_ctor_get(v_snd_3655_, 0);
v_snd_3659_ = lean_ctor_get(v_snd_3655_, 1);
v___x_3660_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3650_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_snd_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3805_; 
v_snd_3661_ = lean_ctor_get(v_b_3647_, 1);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_b_3647_);
if (v_isSharedCheck_3805_ == 0)
{
lean_object* v_unused_3806_; 
v_unused_3806_ = lean_ctor_get(v_b_3647_, 0);
lean_dec(v_unused_3806_);
v___x_3663_ = v_b_3647_;
v_isShared_3664_ = v_isSharedCheck_3805_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_snd_3661_);
lean_dec(v_b_3647_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3805_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3804_; 
v_a_3665_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3667_ = v___x_3660_;
v_isShared_3668_ = v_isSharedCheck_3804_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3660_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3804_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_fst_3669_; lean_object* v_snd_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3803_; 
v_fst_3669_ = lean_ctor_get(v_snd_3661_, 0);
v_snd_3670_ = lean_ctor_get(v_snd_3661_, 1);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_snd_3661_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3672_ = v_snd_3661_;
v_isShared_3673_ = v_isSharedCheck_3803_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_snd_3670_);
lean_inc(v_fst_3669_);
lean_dec(v_snd_3661_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3803_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
uint8_t v_stopAtRfl_3674_; lean_object* v_max_3675_; lean_object* v_minHeartbeats_3676_; lean_object* v_goal_3677_; lean_object* v_target_3678_; uint8_t v_side_3679_; lean_object* v_mctx_3680_; uint8_t v___x_3681_; 
v_stopAtRfl_3674_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*5);
v_max_3675_ = lean_ctor_get(v_cfg_3645_, 0);
v_minHeartbeats_3676_ = lean_ctor_get(v_cfg_3645_, 1);
v_goal_3677_ = lean_ctor_get(v_cfg_3645_, 2);
v_target_3678_ = lean_ctor_get(v_cfg_3645_, 3);
v_side_3679_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*5 + 1);
v_mctx_3680_ = lean_ctor_get(v_cfg_3645_, 4);
v___x_3681_ = lean_nat_dec_lt(v_a_3665_, v_minHeartbeats_3676_);
lean_dec(v_a_3665_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; uint8_t v___x_3683_; 
v___x_3682_ = lean_array_get_size(v_snd_3670_);
v___x_3683_ = lean_nat_dec_le(v_max_3675_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_del_object(v___x_3667_);
v___x_3684_ = lean_box(v_side_3679_);
lean_inc(v_snd_3659_);
lean_inc(v_fst_3658_);
lean_inc(v_fst_3657_);
lean_inc_ref(v_target_3678_);
lean_inc(v_goal_3677_);
lean_inc_ref_n(v_mctx_3680_, 2);
v___x_3685_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3685_, 0, v_mctx_3680_);
lean_closure_set(v___x_3685_, 1, v_goal_3677_);
lean_closure_set(v___x_3685_, 2, v_target_3678_);
lean_closure_set(v___x_3685_, 3, v___x_3684_);
lean_closure_set(v___x_3685_, 4, v_fst_3657_);
lean_closure_set(v___x_3685_, 5, v_fst_3658_);
lean_closure_set(v___x_3685_, 6, v_snd_3659_);
v___x_3686_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3686_, 0, lean_box(0));
lean_closure_set(v___x_3686_, 1, v_mctx_3680_);
lean_closure_set(v___x_3686_, 2, v___x_3685_);
v___x_3687_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3686_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = lean_box(0);
if (lean_obj_tag(v_a_3688_) == 0)
{
lean_object* v___x_3691_; 
if (v_isShared_3673_ == 0)
{
v___x_3691_ = v___x_3672_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_snd_3670_);
v___x_3691_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3691_);
lean_ctor_set(v___x_3663_, 0, v___x_3689_);
v___x_3693_ = v___x_3663_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
v_as_x27_3646_ = v_tail_3656_;
v_b_3647_ = v___x_3693_;
goto _start;
}
}
}
else
{
lean_object* v_val_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3774_; 
v_val_3697_ = lean_ctor_get(v_a_3688_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_a_3688_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3699_ = v_a_3688_;
v_isShared_3700_ = v_isSharedCheck_3774_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_val_3697_);
lean_dec(v_a_3688_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3774_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v_result_3701_; lean_object* v_mctx_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_result_3701_ = lean_ctor_get(v_val_3697_, 2);
v_mctx_3702_ = lean_ctor_get(v_val_3697_, 3);
lean_inc(v_val_3697_);
v___x_3703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3703_, 0, v_val_3697_);
lean_inc_ref(v_mctx_3702_);
v___x_3704_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3704_, 0, lean_box(0));
lean_closure_set(v___x_3704_, 1, v_mctx_3702_);
lean_closure_set(v___x_3704_, 2, v___x_3703_);
v___x_3705_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3704_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; uint8_t v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v___x_3707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3669_, v_a_3706_);
if (v___x_3707_ == 0)
{
lean_object* v_eNew_3708_; lean_object* v___x_3709_; 
v_eNew_3708_ = lean_ctor_get(v_result_3701_, 0);
lean_inc_ref(v_eNew_3708_);
lean_inc_ref(v_mctx_3702_);
v___x_3709_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3702_, v_eNew_3708_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3709_) == 0)
{
if (v_stopAtRfl_3674_ == 0)
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_dec_ref_known(v___x_3709_, 1);
lean_del_object(v___x_3699_);
v___x_3710_ = lean_box(0);
v___x_3711_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3669_, v_a_3706_, v___x_3710_);
v___x_3712_ = lean_array_push(v_snd_3670_, v_val_3697_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 1, v___x_3712_);
lean_ctor_set(v___x_3672_, 0, v___x_3711_);
v___x_3714_ = v___x_3672_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3714_);
lean_ctor_set(v___x_3663_, 0, v___x_3689_);
v___x_3716_ = v___x_3663_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
v_as_x27_3646_ = v_tail_3656_;
v_b_3647_ = v___x_3716_;
goto _start;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3750_; 
v_a_3720_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3722_ = v___x_3709_;
v_isShared_3723_ = v_isSharedCheck_3750_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3709_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3750_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_unbox(v_a_3720_);
lean_dec(v_a_3720_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_del_object(v___x_3722_);
lean_del_object(v___x_3699_);
v___x_3725_ = lean_box(0);
v___x_3726_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3669_, v_a_3706_, v___x_3725_);
v___x_3727_ = lean_array_push(v_snd_3670_, v_val_3697_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 1, v___x_3727_);
lean_ctor_set(v___x_3672_, 0, v___x_3726_);
v___x_3729_ = v___x_3672_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3729_);
lean_ctor_set(v___x_3663_, 0, v___x_3689_);
v___x_3731_ = v___x_3663_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
v_as_x27_3646_ = v_tail_3656_;
v_b_3647_ = v___x_3731_;
goto _start;
}
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
lean_dec(v_a_3706_);
lean_dec_ref(v_cfg_3645_);
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_mk_empty_array_with_capacity(v___x_3735_);
v___x_3737_ = lean_array_push(v___x_3736_, v_val_3697_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3737_);
v___x_3739_ = v___x_3699_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; 
if (v_isShared_3673_ == 0)
{
v___x_3741_ = v___x_3672_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_snd_3670_);
v___x_3741_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3743_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3741_);
lean_ctor_set(v___x_3663_, 0, v___x_3739_);
v___x_3743_ = v___x_3663_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3743_);
v___x_3745_ = v___x_3722_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
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
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v_a_3706_);
lean_del_object(v___x_3699_);
lean_dec(v_val_3697_);
lean_del_object(v___x_3672_);
lean_dec(v_snd_3670_);
lean_dec(v_fst_3669_);
lean_del_object(v___x_3663_);
lean_dec_ref(v_cfg_3645_);
v_a_3751_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3709_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3709_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v___x_3760_; 
lean_dec(v_a_3706_);
lean_del_object(v___x_3699_);
lean_dec(v_val_3697_);
if (v_isShared_3673_ == 0)
{
v___x_3760_ = v___x_3672_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_snd_3670_);
v___x_3760_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3760_);
lean_ctor_set(v___x_3663_, 0, v___x_3689_);
v___x_3762_ = v___x_3663_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
v_as_x27_3646_ = v_tail_3656_;
v_b_3647_ = v___x_3762_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3699_);
lean_dec(v_val_3697_);
lean_del_object(v___x_3672_);
lean_dec(v_snd_3670_);
lean_dec(v_fst_3669_);
lean_del_object(v___x_3663_);
lean_dec_ref(v_cfg_3645_);
v_a_3766_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3705_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3705_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_del_object(v___x_3672_);
lean_dec(v_snd_3670_);
lean_dec(v_fst_3669_);
lean_del_object(v___x_3663_);
lean_dec_ref(v_cfg_3645_);
v_a_3775_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3687_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3687_);
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
else
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_dec_ref(v_cfg_3645_);
lean_inc(v_snd_3670_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_snd_3670_);
if (v_isShared_3673_ == 0)
{
v___x_3785_ = v___x_3672_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_snd_3670_);
v___x_3785_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3785_);
lean_ctor_set(v___x_3663_, 0, v___x_3783_);
v___x_3787_ = v___x_3663_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3789_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3787_);
v___x_3789_ = v___x_3667_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec_ref(v_cfg_3645_);
lean_inc(v_snd_3670_);
v___x_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_snd_3670_);
if (v_isShared_3673_ == 0)
{
v___x_3795_ = v___x_3672_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_snd_3670_);
v___x_3795_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3795_);
lean_ctor_set(v___x_3663_, 0, v___x_3793_);
v___x_3797_ = v___x_3663_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3799_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3797_);
v___x_3799_ = v___x_3667_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
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
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v_b_3647_);
lean_dec_ref(v_cfg_3645_);
v_a_3807_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3660_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3660_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3815_, lean_object* v_as_x27_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3815_, v_as_x27_3816_, v_b_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v_as_x27_3816_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3824_, lean_object* v_seen_3825_, lean_object* v_acc_3826_, lean_object* v_xs_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3833_ = lean_box(0);
v___x_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3834_, 0, v_seen_3825_);
lean_ctor_set(v___x_3834_, 1, v_acc_3826_);
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3833_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3824_, v_xs_3827_, v___x_3835_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3851_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3851_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3851_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_fst_3841_; 
v_fst_3841_ = lean_ctor_get(v_a_3837_, 0);
if (lean_obj_tag(v_fst_3841_) == 0)
{
lean_object* v_snd_3842_; lean_object* v_snd_3843_; lean_object* v___x_3845_; 
v_snd_3842_ = lean_ctor_get(v_a_3837_, 1);
lean_inc(v_snd_3842_);
lean_dec(v_a_3837_);
v_snd_3843_ = lean_ctor_get(v_snd_3842_, 1);
lean_inc(v_snd_3843_);
lean_dec(v_snd_3842_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_snd_3843_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_snd_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
else
{
lean_object* v_val_3847_; lean_object* v___x_3849_; 
lean_inc_ref(v_fst_3841_);
lean_dec(v_a_3837_);
v_val_3847_ = lean_ctor_get(v_fst_3841_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v_fst_3841_, 1);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_val_3847_);
v___x_3849_ = v___x_3839_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_val_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3836_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3836_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3860_, lean_object* v_seen_3861_, lean_object* v_acc_3862_, lean_object* v_xs_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3860_, v_seen_3861_, v_acc_3862_, v_xs_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_xs_3863_);
return v_res_3869_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3870_, lean_object* v_m_3871_, lean_object* v_a_3872_){
_start:
{
uint8_t v___x_3873_; 
v___x_3873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3871_, v_a_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3874_, lean_object* v_m_3875_, lean_object* v_a_3876_){
_start:
{
uint8_t v_res_3877_; lean_object* v_r_3878_; 
v_res_3877_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3874_, v_m_3875_, v_a_3876_);
lean_dec_ref(v_a_3876_);
lean_dec_ref(v_m_3875_);
v_r_3878_ = lean_box(v_res_3877_);
return v_r_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3879_, lean_object* v_m_3880_, lean_object* v_a_3881_, lean_object* v_b_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3880_, v_a_3881_, v_b_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3884_, lean_object* v_as_3885_, lean_object* v_as_x27_3886_, lean_object* v_b_3887_, lean_object* v_a_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3884_, v_as_x27_3886_, v_b_3887_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3895_, lean_object* v_as_3896_, lean_object* v_as_x27_3897_, lean_object* v_b_3898_, lean_object* v_a_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3895_, v_as_3896_, v_as_x27_3897_, v_b_3898_, v_a_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v_as_x27_3897_);
lean_dec(v_as_3896_);
return v_res_3905_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3906_, lean_object* v_a_3907_, lean_object* v_x_3908_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3907_, v_x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3910_, lean_object* v_a_3911_, lean_object* v_x_3912_){
_start:
{
uint8_t v_res_3913_; lean_object* v_r_3914_; 
v_res_3913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3910_, v_a_3911_, v_x_3912_);
lean_dec(v_x_3912_);
lean_dec_ref(v_a_3911_);
v_r_3914_ = lean_box(v_res_3913_);
return v_r_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3915_, lean_object* v_data_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3918_, lean_object* v_a_3919_, lean_object* v_b_3920_, lean_object* v_x_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3919_, v_b_3920_, v_x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3923_, lean_object* v_i_3924_, lean_object* v_source_3925_, lean_object* v_target_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3924_, v_source_3925_, v_target_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_unsigned_to_nat(16u);
v___x_3934_ = lean_mk_array(v___x_3933_, v___x_3932_);
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v___x_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3938_, lean_object* v_moduleRef_3939_, lean_object* v_goal_3940_, lean_object* v_target_3941_, lean_object* v_forbidden_3942_, uint8_t v_side_3943_, uint8_t v_stopAtRfl_3944_, lean_object* v_max_3945_, lean_object* v_leavePercentHeartbeats_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = lean_st_ref_get(v_a_3948_);
lean_inc_ref(v_target_3941_);
v___x_3953_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3938_, v_moduleRef_3939_, v_target_3941_, v_forbidden_3942_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = l_Lean_getMaxHeartbeats___redArg(v_a_3949_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v_mctx_3957_; lean_object* v_minHeartbeats_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v_mctx_3957_ = lean_ctor_get(v___x_3952_, 0);
lean_inc_ref(v_mctx_3957_);
lean_dec(v___x_3952_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = lean_nat_dec_eq(v_a_3956_, v___x_3986_);
lean_dec(v_a_3956_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3949_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = lean_nat_mul(v_leavePercentHeartbeats_3946_, v_a_3989_);
lean_dec(v_a_3989_);
v___x_3991_ = lean_unsigned_to_nat(100u);
v___x_3992_ = lean_nat_div(v___x_3990_, v___x_3991_);
lean_dec(v___x_3990_);
v_minHeartbeats_3959_ = v___x_3992_;
v___y_3960_ = v_a_3947_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_mctx_3957_);
lean_dec(v_a_3954_);
lean_dec(v_max_3945_);
lean_dec_ref(v_target_3941_);
lean_dec(v_goal_3940_);
v_a_3993_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3988_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3988_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
v_minHeartbeats_3959_ = v___x_3986_;
v___y_3960_ = v_a_3947_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
goto v___jp_3958_;
}
v___jp_3958_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_inc(v_max_3945_);
v___x_3964_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3964_, 0, v_max_3945_);
lean_ctor_set(v___x_3964_, 1, v_minHeartbeats_3959_);
lean_ctor_set(v___x_3964_, 2, v_goal_3940_);
lean_ctor_set(v___x_3964_, 3, v_target_3941_);
lean_ctor_set(v___x_3964_, 4, v_mctx_3957_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*5, v_stopAtRfl_3944_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*5 + 1, v_side_3943_);
v___x_3965_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3966_ = lean_mk_empty_array_with_capacity(v_max_3945_);
lean_dec(v_max_3945_);
v___x_3967_ = lean_array_to_list(v_a_3954_);
v___x_3968_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3964_, v___x_3965_, v___x_3966_, v___x_3967_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___x_3967_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3977_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_array_to_list(v_a_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
v_a_3978_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3968_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3968_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_a_3954_);
lean_dec(v___x_3952_);
lean_dec(v_max_3945_);
lean_dec_ref(v_target_3941_);
lean_dec(v_goal_3940_);
v_a_4001_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3955_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3955_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v___x_3952_);
lean_dec(v_max_3945_);
lean_dec_ref(v_target_3941_);
lean_dec(v_goal_3940_);
v_a_4009_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3953_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3953_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4017_, lean_object* v_moduleRef_4018_, lean_object* v_goal_4019_, lean_object* v_target_4020_, lean_object* v_forbidden_4021_, lean_object* v_side_4022_, lean_object* v_stopAtRfl_4023_, lean_object* v_max_4024_, lean_object* v_leavePercentHeartbeats_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
uint8_t v_side_boxed_4031_; uint8_t v_stopAtRfl_boxed_4032_; lean_object* v_res_4033_; 
v_side_boxed_4031_ = lean_unbox(v_side_4022_);
v_stopAtRfl_boxed_4032_ = lean_unbox(v_stopAtRfl_4023_);
v_res_4033_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4017_, v_moduleRef_4018_, v_goal_4019_, v_target_4020_, v_forbidden_4021_, v_side_boxed_4031_, v_stopAtRfl_boxed_4032_, v_max_4024_, v_leavePercentHeartbeats_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_leavePercentHeartbeats_4025_);
lean_dec(v_forbidden_4021_);
return v_res_4033_;
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

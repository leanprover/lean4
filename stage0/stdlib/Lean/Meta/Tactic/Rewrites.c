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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "considering "};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_value;
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
static const lean_string_object l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Candidate rewrite lemmas:\n"};
static const lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__3 = (const lean_object*)&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
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
lean_dec_ref(v_fst_323_);
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
lean_dec_ref(v___x_343_);
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
lean_dec_ref(v___x_388_);
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
lean_dec_ref(v_fst_323_);
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
v___x_482_ = 2ULL;
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
uint8_t v___x_7246__boxed_511_; uint8_t v___x_7249__boxed_512_; lean_object* v_res_513_; 
v___x_7246__boxed_511_ = lean_unbox(v___x_502_);
v___x_7249__boxed_512_ = lean_unbox(v___x_505_);
v_res_513_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_7246__boxed_511_, v___x_503_, v___f_504_, v___x_7249__boxed_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
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
lean_dec_ref(v_name_522_);
lean_dec_ref(v___f_542_);
goto v___jp_537_;
}
}
else
{
lean_dec_ref(v_name_522_);
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
lean_dec_ref(v_name_522_);
lean_dec_ref(v___f_542_);
goto v___jp_537_;
}
}
}
else
{
lean_dec_ref(v_name_522_);
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
lean_dec_ref(v___x_621_);
v___x_623_ = lean_box(0);
v___x_624_ = 0;
v___x_625_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_622_, v___x_623_, v___x_624_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_698_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v___x_625_);
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
lean_dec_ref(v___x_635_);
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
lean_dec_ref(v_fst_638_);
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
lean_dec_ref(v_fst_638_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_inh_807_, lean_object* v_n_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
if (lean_obj_tag(v_n_808_) == 0)
{
lean_object* v_cs_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_849_; 
v_cs_815_ = lean_ctor_get(v_n_808_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_n_808_);
if (v_isSharedCheck_849_ == 0)
{
v___x_817_ = v_n_808_;
v_isShared_818_ = v_isSharedCheck_849_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_cs_815_);
lean_dec(v_n_808_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_849_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; size_t v_sz_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_b_809_);
v_sz_821_ = lean_array_size(v_cs_815_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_inh_807_, v_cs_815_, v_sz_821_, v___x_822_, v___x_820_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v_cs_815_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_840_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_840_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_fst_828_; 
v_fst_828_ = lean_ctor_get(v_a_824_, 0);
if (lean_obj_tag(v_fst_828_) == 0)
{
lean_object* v_snd_829_; lean_object* v___x_831_; 
v_snd_829_ = lean_ctor_get(v_a_824_, 1);
lean_inc(v_snd_829_);
lean_dec(v_a_824_);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 1);
lean_ctor_set(v___x_817_, 0, v_snd_829_);
v___x_831_ = v___x_817_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_snd_829_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_831_);
v___x_833_ = v___x_826_;
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
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; 
lean_inc_ref(v_fst_828_);
lean_dec(v_a_824_);
lean_del_object(v___x_817_);
v_val_836_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_val_836_);
lean_dec_ref(v_fst_828_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_val_836_);
v___x_838_ = v___x_826_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_del_object(v___x_817_);
v_a_841_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_823_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_823_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
else
{
lean_object* v_vs_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_884_; 
v_vs_850_ = lean_ctor_get(v_n_808_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_n_808_);
if (v_isSharedCheck_884_ == 0)
{
v___x_852_ = v_n_808_;
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_vs_850_);
lean_dec(v_n_808_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_b_809_);
v_sz_856_ = lean_array_size(v_vs_850_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_850_, v_sz_856_, v___x_857_, v___x_855_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v_vs_850_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_875_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_875_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; 
v_fst_863_ = lean_ctor_get(v_a_859_, 0);
if (lean_obj_tag(v_fst_863_) == 0)
{
lean_object* v_snd_864_; lean_object* v___x_866_; 
v_snd_864_ = lean_ctor_get(v_a_859_, 1);
lean_inc(v_snd_864_);
lean_dec(v_a_859_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_snd_864_);
v___x_866_ = v___x_852_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_snd_864_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_866_);
v___x_868_ = v___x_861_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v_val_871_; lean_object* v___x_873_; 
lean_inc_ref(v_fst_863_);
lean_dec(v_a_859_);
lean_del_object(v___x_852_);
v_val_871_ = lean_ctor_get(v_fst_863_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v_fst_863_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_val_871_);
v___x_873_ = v___x_861_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_val_871_);
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
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_852_);
v_a_876_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_858_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_858_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_inh_885_, lean_object* v_as_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_889_);
return v___x_896_;
}
else
{
lean_object* v_snd_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_931_; 
v_snd_897_ = lean_ctor_get(v_b_889_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_b_889_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_b_889_, 0);
lean_dec(v_unused_932_);
v___x_899_ = v_b_889_;
v_isShared_900_ = v_isSharedCheck_931_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snd_897_);
lean_dec(v_b_889_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_931_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_array_uget_borrowed(v_as_886_, v_i_888_);
lean_inc(v_snd_897_);
lean_inc(v_a_901_);
v___x_902_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_inh_885_, v_a_901_, v_snd_897_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_922_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
if (lean_obj_tag(v_a_903_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v_a_903_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_907_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_snd_897_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_909_);
v___x_911_ = v___x_905_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
lean_del_object(v___x_905_);
lean_dec(v_snd_897_);
v_a_914_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v_a_903_);
v___x_915_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v_a_914_);
lean_ctor_set(v___x_899_, 0, v___x_915_);
v___x_917_ = v___x_899_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_914_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
size_t v___x_918_; size_t v___x_919_; 
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_888_, v___x_918_);
v_i_888_ = v___x_919_;
v_b_889_ = v___x_917_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_899_);
lean_dec(v_snd_897_);
v_a_923_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_902_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_902_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_inh_933_, lean_object* v_as_934_, lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_sz_boxed_943_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_944_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_inh_933_, v_as_934_, v_sz_boxed_943_, v_i_boxed_944_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_as_934_);
lean_dec_ref(v_inh_933_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_inh_946_, lean_object* v_n_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_inh_946_, v_n_947_, v_b_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_inh_946_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_955_, size_t v_sz_956_, size_t v_i_957_, lean_object* v_b_958_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_lt(v_i_957_, v_sz_956_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_b_958_);
return v___x_961_;
}
else
{
lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_980_; 
v_snd_962_ = lean_ctor_get(v_b_958_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_b_958_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_b_958_, 0);
lean_dec(v_unused_981_);
v___x_964_ = v_b_958_;
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_dec(v_b_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v_a_968_; lean_object* v_a_975_; 
v___x_966_ = lean_box(0);
v_a_975_ = lean_array_uget_borrowed(v_as_955_, v_i_957_);
if (lean_obj_tag(v_a_975_) == 0)
{
v_a_968_ = v_snd_962_;
goto v___jp_967_;
}
else
{
lean_object* v_val_976_; uint8_t v___x_977_; 
v_val_976_ = lean_ctor_get(v_a_975_, 0);
v___x_977_ = l_Lean_LocalDecl_isImplementationDetail(v_val_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; 
lean_inc(v_val_976_);
v___x_978_ = l_Lean_LocalDecl_toExpr(v_val_976_);
v___x_979_ = lean_array_push(v_snd_962_, v___x_978_);
v_a_968_ = v___x_979_;
goto v___jp_967_;
}
else
{
v_a_968_ = v_snd_962_;
goto v___jp_967_;
}
}
v___jp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_a_968_);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_970_ = v___x_964_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_968_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
size_t v___x_971_; size_t v___x_972_; 
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_add(v_i_957_, v___x_971_);
v_i_957_ = v___x_972_;
v_b_958_ = v___x_970_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_){
_start:
{
size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_sz_boxed_987_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_988_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_982_, v_sz_boxed_987_, v_i_boxed_988_, v_b_985_);
lean_dec_ref(v_as_982_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_990_, size_t v_sz_991_, size_t v_i_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = lean_usize_dec_lt(v_i_992_, v_sz_991_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_b_993_);
return v___x_1000_;
}
else
{
lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1019_; 
v_snd_1001_ = lean_ctor_get(v_b_993_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_b_993_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_b_993_, 0);
lean_dec(v_unused_1020_);
v___x_1003_ = v_b_993_;
v_isShared_1004_ = v_isSharedCheck_1019_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_dec(v_b_993_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1019_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v_a_1007_; lean_object* v_a_1014_; 
v___x_1005_ = lean_box(0);
v_a_1014_ = lean_array_uget_borrowed(v_as_990_, v_i_992_);
if (lean_obj_tag(v_a_1014_) == 0)
{
v_a_1007_ = v_snd_1001_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1015_; uint8_t v___x_1016_; 
v_val_1015_ = lean_ctor_get(v_a_1014_, 0);
v___x_1016_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_inc(v_val_1015_);
v___x_1017_ = l_Lean_LocalDecl_toExpr(v_val_1015_);
v___x_1018_ = lean_array_push(v_snd_1001_, v___x_1017_);
v_a_1007_ = v___x_1018_;
goto v___jp_1006_;
}
else
{
v_a_1007_ = v_snd_1001_;
goto v___jp_1006_;
}
}
v___jp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v_a_1007_);
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1009_ = v___x_1003_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_1007_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_992_, v___x_1010_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_990_, v_sz_991_, v___x_1011_, v___x_1009_);
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1021_, lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_1021_, v_sz_boxed_1030_, v_i_boxed_1031_, v_b_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v_as_1021_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1033_, lean_object* v_init_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_root_1040_; lean_object* v_tail_1041_; lean_object* v___x_1042_; 
v_root_1040_ = lean_ctor_get(v_t_1033_, 0);
lean_inc_ref(v_root_1040_);
v_tail_1041_ = lean_ctor_get(v_t_1033_, 1);
lean_inc_ref(v_tail_1041_);
lean_dec_ref(v_t_1033_);
lean_inc_ref(v_init_1034_);
v___x_1042_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1034_, v_root_1040_, v_init_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v_init_1034_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1079_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1079_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1079_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
if (lean_obj_tag(v_a_1043_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; 
lean_dec_ref(v_tail_1041_);
v_a_1047_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v_a_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_a_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1047_);
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
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; size_t v_sz_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
lean_del_object(v___x_1045_);
v_a_1051_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v_a_1043_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_a_1051_);
v_sz_1054_ = lean_array_size(v_tail_1041_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1041_, v_sz_1054_, v___x_1055_, v___x_1053_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v_tail_1041_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1070_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1070_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1070_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_fst_1061_; 
v_fst_1061_ = lean_ctor_get(v_a_1057_, 0);
if (lean_obj_tag(v_fst_1061_) == 0)
{
lean_object* v_snd_1062_; lean_object* v___x_1064_; 
v_snd_1062_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_snd_1062_);
lean_dec(v_a_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_snd_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_snd_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v_val_1066_; lean_object* v___x_1068_; 
lean_inc_ref(v_fst_1061_);
lean_dec(v_a_1057_);
v_val_1066_ = lean_ctor_get(v_fst_1061_, 0);
lean_inc(v_val_1066_);
lean_dec_ref(v_fst_1061_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_val_1066_);
v___x_1068_ = v___x_1059_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_val_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1056_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1056_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_tail_1041_);
v_a_1080_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1042_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1042_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1088_, lean_object* v_init_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1088_, v_init_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_lctx_1103_; lean_object* v_decls_1104_; lean_object* v_hs_1105_; lean_object* v___x_1106_; 
v_lctx_1103_ = lean_ctor_get(v___y_1098_, 2);
v_decls_1104_ = lean_ctor_get(v_lctx_1103_, 1);
lean_inc_ref(v_decls_1104_);
v_hs_1105_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1106_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1104_, v_hs_1105_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___y_1098_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc_ref(v_a_1116_);
v___x_1121_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1124_ = lean_array_size(v_a_1122_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1115_, v_a_1122_, v_sz_1124_, v___x_1125_, v___x_1123_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1122_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1121_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_except_1135_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1142_, v_sz_1143_, v_i_1144_, v_b_1145_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1152_, v_sz_boxed_1161_, v_i_boxed_1162_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_as_1152_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1164_, size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1164_, v_sz_1165_, v_i_1166_, v_b_1167_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1174_, lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1174_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_as_1174_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1217_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1216_, v___x_1217_, v___x_1218_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_st_mk_ref(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2____boxed(lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState(void){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object* v___x_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_st_mk_ref(v___x_1233_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object* v___x_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(v___x_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_box(0);
v___f_1244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_));
v___x_1245_ = lean_box(2);
v___x_1246_ = l_Lean_registerEnvExtension___redArg(v___f_1244_, v___x_1243_, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
return v_res_1248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_unsigned_to_nat(6500u);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
lean_object* v_snd_1252_; uint8_t v___x_1253_; 
v_snd_1252_ = lean_ctor_get(v_x_1251_, 1);
v___x_1253_ = lean_unbox(v_snd_1252_);
if (v___x_1253_ == 0)
{
lean_object* v_fst_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1266_; 
v_fst_1254_ = lean_ctor_get(v_x_1251_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_x_1251_, 1);
lean_dec(v_unused_1267_);
v___x_1256_ = v_x_1251_;
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_fst_1254_);
lean_dec(v_x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1258_ = 0;
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_nat_mul(v___x_1259_, v_x_1250_);
lean_dec(v_x_1250_);
v___x_1261_ = lean_box(v___x_1258_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1260_);
lean_ctor_set(v___x_1256_, 0, v___x_1261_);
v___x_1263_ = v___x_1256_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1260_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_fst_1254_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
return v___x_1264_;
}
}
}
else
{
lean_object* v_fst_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_fst_1268_ = lean_ctor_get(v_x_1251_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_x_1251_, 1);
lean_dec(v_unused_1279_);
v___x_1270_ = v_x_1251_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_fst_1268_);
lean_dec(v_x_1251_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = 1;
v___x_1273_ = lean_box(v___x_1272_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_x_1250_);
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_x_1250_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_fst_1268_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1281_, lean_object* v_ty_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1288_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1289_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1290_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1291_ = lean_unsigned_to_nat(6500u);
v___x_1292_ = lean_box(0);
v___x_1293_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1294_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1281_, v___x_1288_, v___x_1289_, v___x_1290_, v___x_1291_, v___x_1292_, v___x_1293_, v_ty_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1295_, lean_object* v_ty_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1295_, v_ty_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1303_, v_x_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1327_, v_x_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1335_, lean_object* v_mctx_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1336_, v_x_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_mctx_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1344_, v_mctx_1345_, v_x_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Meta_saveState___redArg(v___y_1355_, v___y_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v_r_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
v_r_1361_ = lean_apply_5(v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
if (lean_obj_tag(v_r_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v_r_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v_r_1361_);
v___x_1363_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1360_, v___y_1355_, v___y_1357_);
lean_dec(v_a_1360_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1371_);
v___x_1365_ = v___x_1363_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v___x_1363_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v_a_1362_);
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1362_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_a_1362_);
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v_r_1361_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v_r_1361_);
v___x_1381_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1360_, v___y_1355_, v___y_1357_);
lean_dec(v_a_1360_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1389_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
lean_ctor_set(v___x_1383_, 0, v_a_1380_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1380_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1380_);
v_a_1390_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1381_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1381_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_x_1353_);
v_a_1398_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1359_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1359_);
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1421_, v_x_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1429_; uint64_t v___x_1430_; 
v___x_1429_ = 2;
v___x_1430_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1431_, uint8_t v___x_1432_, lean_object* v___x_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_mkFreshExprMVar(v___x_1431_, v___x_1432_, v___x_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; uint8_t v_foApprox_1442_; uint8_t v_ctxApprox_1443_; uint8_t v_quasiPatternApprox_1444_; uint8_t v_constApprox_1445_; uint8_t v_isDefEqStuckEx_1446_; uint8_t v_unificationHints_1447_; uint8_t v_proofIrrelevance_1448_; uint8_t v_assignSyntheticOpaque_1449_; uint8_t v_offsetCnstrs_1450_; uint8_t v_etaStruct_1451_; uint8_t v_univApprox_1452_; uint8_t v_iota_1453_; uint8_t v_beta_1454_; uint8_t v_proj_1455_; uint8_t v_zeta_1456_; uint8_t v_zetaDelta_1457_; uint8_t v_zetaUnused_1458_; uint8_t v_zetaHave_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1518_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = l_Lean_Meta_Context_config(v___y_1434_);
v_foApprox_1442_ = lean_ctor_get_uint8(v___x_1441_, 0);
v_ctxApprox_1443_ = lean_ctor_get_uint8(v___x_1441_, 1);
v_quasiPatternApprox_1444_ = lean_ctor_get_uint8(v___x_1441_, 2);
v_constApprox_1445_ = lean_ctor_get_uint8(v___x_1441_, 3);
v_isDefEqStuckEx_1446_ = lean_ctor_get_uint8(v___x_1441_, 4);
v_unificationHints_1447_ = lean_ctor_get_uint8(v___x_1441_, 5);
v_proofIrrelevance_1448_ = lean_ctor_get_uint8(v___x_1441_, 6);
v_assignSyntheticOpaque_1449_ = lean_ctor_get_uint8(v___x_1441_, 7);
v_offsetCnstrs_1450_ = lean_ctor_get_uint8(v___x_1441_, 8);
v_etaStruct_1451_ = lean_ctor_get_uint8(v___x_1441_, 10);
v_univApprox_1452_ = lean_ctor_get_uint8(v___x_1441_, 11);
v_iota_1453_ = lean_ctor_get_uint8(v___x_1441_, 12);
v_beta_1454_ = lean_ctor_get_uint8(v___x_1441_, 13);
v_proj_1455_ = lean_ctor_get_uint8(v___x_1441_, 14);
v_zeta_1456_ = lean_ctor_get_uint8(v___x_1441_, 15);
v_zetaDelta_1457_ = lean_ctor_get_uint8(v___x_1441_, 16);
v_zetaUnused_1458_ = lean_ctor_get_uint8(v___x_1441_, 17);
v_zetaHave_1459_ = lean_ctor_get_uint8(v___x_1441_, 18);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1461_ = v___x_1441_;
v_isShared_1462_ = v_isSharedCheck_1518_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v___x_1441_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1518_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
uint8_t v_trackZetaDelta_1463_; lean_object* v_zetaDeltaSet_1464_; lean_object* v_lctx_1465_; lean_object* v_localInstances_1466_; lean_object* v_defEqCtx_x3f_1467_; lean_object* v_synthPendingDepth_1468_; lean_object* v_canUnfold_x3f_1469_; uint8_t v_univApprox_1470_; uint8_t v_inTypeClassResolution_1471_; uint8_t v_cacheInferType_1472_; uint8_t v___x_1473_; lean_object* v_config_1475_; 
v_trackZetaDelta_1463_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*7);
v_zetaDeltaSet_1464_ = lean_ctor_get(v___y_1434_, 1);
lean_inc(v_zetaDeltaSet_1464_);
v_lctx_1465_ = lean_ctor_get(v___y_1434_, 2);
lean_inc_ref(v_lctx_1465_);
v_localInstances_1466_ = lean_ctor_get(v___y_1434_, 3);
lean_inc_ref(v_localInstances_1466_);
v_defEqCtx_x3f_1467_ = lean_ctor_get(v___y_1434_, 4);
lean_inc(v_defEqCtx_x3f_1467_);
v_synthPendingDepth_1468_ = lean_ctor_get(v___y_1434_, 5);
lean_inc(v_synthPendingDepth_1468_);
v_canUnfold_x3f_1469_ = lean_ctor_get(v___y_1434_, 6);
lean_inc(v_canUnfold_x3f_1469_);
v_univApprox_1470_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1471_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*7 + 2);
v_cacheInferType_1472_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*7 + 3);
v___x_1473_ = 2;
if (v_isShared_1462_ == 0)
{
v_config_1475_ = v___x_1461_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 0, v_foApprox_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 1, v_ctxApprox_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 2, v_quasiPatternApprox_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 3, v_constApprox_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 4, v_isDefEqStuckEx_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 5, v_unificationHints_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 6, v_proofIrrelevance_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 7, v_assignSyntheticOpaque_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 8, v_offsetCnstrs_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 10, v_etaStruct_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 11, v_univApprox_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 12, v_iota_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 13, v_beta_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 14, v_proj_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 15, v_zeta_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 16, v_zetaDelta_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 17, v_zetaUnused_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, 18, v_zetaHave_1459_);
v_config_1475_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
uint64_t v___x_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1509_; 
lean_ctor_set_uint8(v_config_1475_, 9, v___x_1473_);
v___x_1476_ = l_Lean_Meta_Context_configKey(v___y_1434_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___y_1434_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1510_ = lean_ctor_get(v___y_1434_, 6);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v___y_1434_, 5);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v___y_1434_, 4);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v___y_1434_, 3);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v___y_1434_, 2);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v___y_1434_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v___y_1434_, 0);
lean_dec(v_unused_1516_);
v___x_1478_ = v___y_1434_;
v_isShared_1479_ = v_isSharedCheck_1509_;
goto v_resetjp_1477_;
}
else
{
lean_dec(v___y_1434_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1509_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
uint64_t v___x_1480_; uint64_t v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; uint64_t v___x_1484_; uint64_t v___x_1485_; uint64_t v_key_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1480_ = 2ULL;
v___x_1481_ = lean_uint64_shift_right(v___x_1476_, v___x_1480_);
v___x_1482_ = l_Lean_Expr_mvarId_x21(v_a_1440_);
lean_dec(v_a_1440_);
v___x_1483_ = 1;
v___x_1484_ = lean_uint64_shift_left(v___x_1481_, v___x_1480_);
v___x_1485_ = lean_uint64_once(&l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0, &l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0);
v_key_1486_ = lean_uint64_lor(v___x_1484_, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1487_, 0, v_config_1475_);
lean_ctor_set_uint64(v___x_1487_, sizeof(void*)*1, v_key_1486_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1487_);
v___x_1489_ = v___x_1478_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_zetaDeltaSet_1464_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_lctx_1465_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_localInstances_1466_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_defEqCtx_x3f_1467_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_synthPendingDepth_1468_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_canUnfold_x3f_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*7, v_trackZetaDelta_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*7 + 1, v_univApprox_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*7 + 3, v_cacheInferType_1472_);
v___x_1489_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_MVarId_refl(v___x_1482_, v___x_1483_, v___x_1489_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec_ref(v___x_1489_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v___x_1490_, 0);
lean_dec(v_unused_1499_);
v___x_1492_ = v___x_1490_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v___x_1490_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(v___x_1483_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1490_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1490_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
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
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___y_1434_);
v_a_1519_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1439_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1439_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v___x_2362__boxed_1535_; lean_object* v_res_1536_; 
v___x_2362__boxed_1535_ = lean_unbox(v___x_1528_);
v_res_1536_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1527_, v___x_2362__boxed_1535_, v___x_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1537_, lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_e_1538_);
v___x_1545_ = 0;
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_box(v___x_1545_);
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1548_, 0, v___x_1544_);
lean_closure_set(v___f_1548_, 1, v___x_1547_);
lean_closure_set(v___f_1548_, 2, v___x_1546_);
v___x_1549_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1549_, 0, lean_box(0));
lean_closure_set(v___x_1549_, 1, v_mctx_1537_);
lean_closure_set(v___x_1549_, 2, v___f_1548_);
v___x_1550_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1549_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
if (lean_obj_tag(v___x_1550_) == 0)
{
return v___x_1550_;
}
else
{
lean_object* v_a_1551_; uint8_t v___y_1553_; uint8_t v___x_1563_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
v___x_1563_ = l_Lean_Exception_isInterrupt(v_a_1551_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; 
v___x_1564_ = l_Lean_Exception_isRuntime(v_a_1551_);
v___y_1553_ = v___x_1564_;
goto v___jp_1552_;
}
else
{
lean_dec(v_a_1551_);
v___y_1553_ = v___x_1563_;
goto v___jp_1552_;
}
v___jp_1552_:
{
if (v___y_1553_ == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1562_);
v___x_1555_ = v___x_1550_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(v___y_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1565_, lean_object* v_e_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1565_, v_e_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_result_1579_; lean_object* v_eNew_1580_; lean_object* v___x_1581_; 
v_result_1579_ = lean_ctor_get(v_r_1573_, 2);
lean_inc_ref(v_result_1579_);
lean_dec_ref(v_r_1573_);
v_eNew_1580_ = lean_ctor_get(v_result_1579_, 0);
lean_inc_ref(v_eNew_1580_);
lean_dec_ref(v_result_1579_);
v___x_1581_ = l_Lean_Meta_ppExpr(v_eNew_1580_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1592_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1586_ = l_Std_Format_defWidth;
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = l_Std_Format_pretty(v_a_1582_, v___x_1586_, v___x_1587_, v___x_1587_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1590_ = v___x_1584_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1581_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1581_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1608_){
_start:
{
switch(v_x_1608_)
{
case 0:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
return v___x_1609_;
}
case 1:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
return v___x_1610_;
}
default: 
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_unsigned_to_nat(2u);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1612_){
_start:
{
uint8_t v_x_boxed_1613_; lean_object* v_res_1614_; 
v_x_boxed_1613_ = lean_unbox(v_x_1612_);
v_res_1614_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1617_){
_start:
{
uint8_t v_x_4__boxed_1618_; lean_object* v_res_1619_; 
v_x_4__boxed_1618_ = lean_unbox(v_x_1617_);
v_res_1619_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1620_){
_start:
{
lean_inc(v_k_1620_);
return v_k_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1621_);
lean_dec(v_k_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1623_, lean_object* v_ctorIdx_1624_, uint8_t v_t_1625_, lean_object* v_h_1626_, lean_object* v_k_1627_){
_start:
{
lean_inc(v_k_1627_);
return v_k_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1628_, lean_object* v_ctorIdx_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_k_1632_){
_start:
{
uint8_t v_t_boxed_1633_; lean_object* v_res_1634_; 
v_t_boxed_1633_ = lean_unbox(v_t_1630_);
v_res_1634_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1628_, v_ctorIdx_1629_, v_t_boxed_1633_, v_h_1631_, v_k_1632_);
lean_dec(v_k_1632_);
lean_dec(v_ctorIdx_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1635_){
_start:
{
lean_inc(v_none_1635_);
return v_none_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1636_);
lean_dec(v_none_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1638_, uint8_t v_t_1639_, lean_object* v_h_1640_, lean_object* v_none_1641_){
_start:
{
lean_inc(v_none_1641_);
return v_none_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_none_1645_){
_start:
{
uint8_t v_t_boxed_1646_; lean_object* v_res_1647_; 
v_t_boxed_1646_ = lean_unbox(v_t_1643_);
v_res_1647_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1642_, v_t_boxed_1646_, v_h_1644_, v_none_1645_);
lean_dec(v_none_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1648_){
_start:
{
lean_inc(v_assumption_1648_);
return v_assumption_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1649_);
lean_dec(v_assumption_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1651_, uint8_t v_t_1652_, lean_object* v_h_1653_, lean_object* v_assumption_1654_){
_start:
{
lean_inc(v_assumption_1654_);
return v_assumption_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1655_, lean_object* v_t_1656_, lean_object* v_h_1657_, lean_object* v_assumption_1658_){
_start:
{
uint8_t v_t_boxed_1659_; lean_object* v_res_1660_; 
v_t_boxed_1659_ = lean_unbox(v_t_1656_);
v_res_1660_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1655_, v_t_boxed_1659_, v_h_1657_, v_assumption_1658_);
lean_dec(v_assumption_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1661_){
_start:
{
lean_inc(v_solveByElim_1661_);
return v_solveByElim_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1662_);
lean_dec(v_solveByElim_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1664_, uint8_t v_t_1665_, lean_object* v_h_1666_, lean_object* v_solveByElim_1667_){
_start:
{
lean_inc(v_solveByElim_1667_);
return v_solveByElim_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1668_, lean_object* v_t_1669_, lean_object* v_h_1670_, lean_object* v_solveByElim_1671_){
_start:
{
uint8_t v_t_boxed_1672_; lean_object* v_res_1673_; 
v_t_boxed_1672_ = lean_unbox(v_t_1669_);
v_res_1673_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1668_, v_t_boxed_1672_, v_h_1670_, v_solveByElim_1671_);
lean_dec(v_solveByElim_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1683_, v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_x_1684_);
lean_dec(v_x_1683_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = 0;
v___x_1698_ = lean_box(v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v_x_1700_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v_env_1714_; lean_object* v___x_1715_; lean_object* v_mctx_1716_; lean_object* v_lctx_1717_; lean_object* v_options_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1713_ = lean_st_ref_get(v___y_1711_);
v_env_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc_ref(v_env_1714_);
lean_dec(v___x_1713_);
v___x_1715_ = lean_st_ref_get(v___y_1709_);
v_mctx_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc_ref(v_mctx_1716_);
lean_dec(v___x_1715_);
v_lctx_1717_ = lean_ctor_get(v___y_1708_, 2);
v_options_1718_ = lean_ctor_get(v___y_1710_, 2);
lean_inc_ref(v_options_1718_);
lean_inc_ref(v_lctx_1717_);
v___x_1719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1719_, 0, v_env_1714_);
lean_ctor_set(v___x_1719_, 1, v_mctx_1716_);
lean_ctor_set(v___x_1719_, 2, v_lctx_1717_);
lean_ctor_set(v___x_1719_, 3, v_options_1718_);
v___x_1720_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v_msgData_1707_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_ref_1735_; lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
v_ref_1735_ = lean_ctor_get(v___y_1732_, 5);
v___x_1736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_inc(v_ref_1735_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_ref_1735_);
lean_ctor_set(v___x_1741_, 1, v_a_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 1);
lean_ctor_set(v___x_1739_, 0, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1752_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1763_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1762_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v_x_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1780_, lean_object* v_depth_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___f_1787_; lean_object* v___f_1788_; lean_object* v___f_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v_cfg_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___f_1787_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1788_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1789_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1790_ = 0;
v___x_1791_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1791_, 0, v_depth_1781_);
lean_ctor_set(v___x_1791_, 1, v___f_1787_);
lean_ctor_set(v___x_1791_, 2, v___f_1788_);
lean_ctor_set(v___x_1791_, 3, v___f_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*4, v___x_1790_);
v___x_1792_ = 1;
v___x_1793_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1794_ = 1;
v___x_1795_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1795_, 0, v___x_1791_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*2, v___x_1794_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*2 + 1, v___x_1792_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*2 + 2, v___x_1790_);
v_cfg_1796_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1796_, 0, v___x_1795_);
lean_ctor_set_uint8(v_cfg_1796_, sizeof(void*)*1, v___x_1792_);
lean_ctor_set_uint8(v_cfg_1796_, sizeof(void*)*1 + 1, v___x_1792_);
lean_ctor_set_uint8(v_cfg_1796_, sizeof(void*)*1 + 2, v___x_1792_);
lean_ctor_set_uint8(v_cfg_1796_, sizeof(void*)*1 + 3, v___x_1790_);
v___x_1797_ = lean_box(0);
v___x_1798_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1799_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1790_, v___x_1790_, v___x_1797_, v___x_1797_, v___x_1798_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v_fst_1801_; lean_object* v_snd_1802_; lean_object* v___x_1803_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v_fst_1801_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_fst_1801_);
v_snd_1802_ = lean_ctor_get(v_a_1800_, 1);
lean_inc(v_snd_1802_);
lean_dec(v_a_1800_);
v___x_1803_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1796_, v_fst_1801_, v_snd_1802_, v_goals_1780_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1814_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
if (lean_obj_tag(v_a_1804_) == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_box(0);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1810_ = v___x_1806_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_del_object(v___x_1806_);
lean_dec(v_a_1804_);
v___x_1812_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1813_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1812_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1803_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1803_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_cfg_1796_);
lean_dec(v_goals_1780_);
v_a_1823_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1799_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1799_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1831_, lean_object* v_depth_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1831_, v_depth_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1847_, v_msg_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Expr_hasMVar(v_e_1855_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_e_1855_);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v_mctx_1861_; lean_object* v___x_1862_; lean_object* v_fst_1863_; lean_object* v_snd_1864_; lean_object* v___x_1865_; lean_object* v_cache_1866_; lean_object* v_zetaDeltaFVarIds_1867_; lean_object* v_postponed_1868_; lean_object* v_diag_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
v___x_1860_ = lean_st_ref_get(v___y_1856_);
v_mctx_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_mctx_1861_);
lean_dec(v___x_1860_);
v___x_1862_ = l_Lean_instantiateMVarsCore(v_mctx_1861_, v_e_1855_);
v_fst_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_fst_1863_);
v_snd_1864_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_snd_1864_);
lean_dec_ref(v___x_1862_);
v___x_1865_ = lean_st_ref_take(v___y_1856_);
v_cache_1866_ = lean_ctor_get(v___x_1865_, 1);
v_zetaDeltaFVarIds_1867_ = lean_ctor_get(v___x_1865_, 2);
v_postponed_1868_ = lean_ctor_get(v___x_1865_, 3);
v_diag_1869_ = lean_ctor_get(v___x_1865_, 4);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1865_, 0);
lean_dec(v_unused_1879_);
v___x_1871_ = v___x_1865_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_diag_1869_);
lean_inc(v_postponed_1868_);
lean_inc(v_zetaDeltaFVarIds_1867_);
lean_inc(v_cache_1866_);
lean_dec(v___x_1865_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v_snd_1864_);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_snd_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_zetaDeltaFVarIds_1867_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_postponed_1868_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v_diag_1869_);
v___x_1874_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_st_ref_set(v___y_1856_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_fst_1863_);
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1880_, v___y_1881_);
lean_dec(v___y_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1884_, v___y_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(lean_object* v_cls_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_options_1904_; uint8_t v_hasTrace_1905_; 
v_options_1904_ = lean_ctor_get(v___y_1902_, 2);
v_hasTrace_1905_ = lean_ctor_get_uint8(v_options_1904_, sizeof(void*)*1);
if (v_hasTrace_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v_cls_1901_);
v___x_1906_ = lean_box(v_hasTrace_1905_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
else
{
lean_object* v_inheritedTraceOptions_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_inheritedTraceOptions_1908_ = lean_ctor_get(v___y_1902_, 13);
v___x_1909_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___closed__1));
v___x_1910_ = l_Lean_Name_append(v___x_1909_, v_cls_1901_);
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1908_, v_options_1904_, v___x_1910_);
lean_dec(v___x_1910_);
v___x_1912_ = lean_box(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg___boxed(lean_object* v_cls_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(v_cls_1914_, v___y_1915_);
lean_dec_ref(v___y_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(v_cls_1918_, v___y_1921_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = l_List_reverse___redArg(v_x_1933_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v_head_1941_; lean_object* v_tail_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1960_; 
v_head_1941_ = lean_ctor_get(v_x_1932_, 0);
v_tail_1942_ = lean_ctor_get(v_x_1932_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1944_ = v_x_1932_;
v_isShared_1945_ = v_isSharedCheck_1960_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_tail_1942_);
lean_inc(v_head_1941_);
lean_dec(v_x_1932_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1960_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_MVarId_assumption(v_head_1941_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_x_1933_);
lean_ctor_set(v___x_1944_, 0, v_a_1947_);
v___x_1949_ = v___x_1944_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1947_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_x_1933_);
v___x_1949_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
v_x_1932_ = v_tail_1942_;
v_x_1933_ = v___x_1949_;
goto _start;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_del_object(v___x_1944_);
lean_dec(v_tail_1942_);
lean_dec(v_x_1933_);
v_a_1952_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1946_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1946_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1961_, v_x_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1968_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1969_; double v___x_1970_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_float_of_nat(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3(lean_object* v_cls_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_ref_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2027_; 
v_ref_1981_ = lean_ctor_get(v___y_1978_, 5);
v___x_1982_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2027_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2027_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v_traceState_1988_; lean_object* v_env_1989_; lean_object* v_nextMacroScope_1990_; lean_object* v_ngen_1991_; lean_object* v_auxDeclNGen_1992_; lean_object* v_cache_1993_; lean_object* v_messages_1994_; lean_object* v_infoState_1995_; lean_object* v_snapshotTasks_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2026_; 
v___x_1987_ = lean_st_ref_take(v___y_1979_);
v_traceState_1988_ = lean_ctor_get(v___x_1987_, 4);
v_env_1989_ = lean_ctor_get(v___x_1987_, 0);
v_nextMacroScope_1990_ = lean_ctor_get(v___x_1987_, 1);
v_ngen_1991_ = lean_ctor_get(v___x_1987_, 2);
v_auxDeclNGen_1992_ = lean_ctor_get(v___x_1987_, 3);
v_cache_1993_ = lean_ctor_get(v___x_1987_, 5);
v_messages_1994_ = lean_ctor_get(v___x_1987_, 6);
v_infoState_1995_ = lean_ctor_get(v___x_1987_, 7);
v_snapshotTasks_1996_ = lean_ctor_get(v___x_1987_, 8);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1998_ = v___x_1987_;
v_isShared_1999_ = v_isSharedCheck_2026_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_snapshotTasks_1996_);
lean_inc(v_infoState_1995_);
lean_inc(v_messages_1994_);
lean_inc(v_cache_1993_);
lean_inc(v_traceState_1988_);
lean_inc(v_auxDeclNGen_1992_);
lean_inc(v_ngen_1991_);
lean_inc(v_nextMacroScope_1990_);
lean_inc(v_env_1989_);
lean_dec(v___x_1987_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2026_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
uint64_t v_tid_2000_; lean_object* v_traces_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2025_; 
v_tid_2000_ = lean_ctor_get_uint64(v_traceState_1988_, sizeof(void*)*1);
v_traces_2001_ = lean_ctor_get(v_traceState_1988_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_traceState_1988_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2003_ = v_traceState_1988_;
v_isShared_2004_ = v_isSharedCheck_2025_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_traces_2001_);
lean_dec(v_traceState_1988_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2025_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; double v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__0);
v___x_2007_ = 0;
v___x_2008_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__1));
v___x_2009_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2009_, 0, v_cls_1974_);
lean_ctor_set(v___x_2009_, 1, v___x_2005_);
lean_ctor_set(v___x_2009_, 2, v___x_2008_);
lean_ctor_set_float(v___x_2009_, sizeof(void*)*3, v___x_2006_);
lean_ctor_set_float(v___x_2009_, sizeof(void*)*3 + 8, v___x_2006_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*3 + 16, v___x_2007_);
v___x_2010_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__2));
v___x_2011_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v_a_1983_);
lean_ctor_set(v___x_2011_, 2, v___x_2010_);
lean_inc(v_ref_1981_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_ref_1981_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = l_Lean_PersistentArray_push___redArg(v_traces_2001_, v___x_2012_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2013_);
v___x_2015_ = v___x_2003_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2013_);
lean_ctor_set_uint64(v_reuseFailAlloc_2024_, sizeof(void*)*1, v_tid_2000_);
v___x_2015_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 4, v___x_2015_);
v___x_2017_ = v___x_1998_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_env_1989_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_nextMacroScope_1990_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_ngen_1991_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_auxDeclNGen_1992_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2023_, 5, v_cache_1993_);
lean_ctor_set(v_reuseFailAlloc_2023_, 6, v_messages_1994_);
lean_ctor_set(v_reuseFailAlloc_2023_, 7, v_infoState_1995_);
lean_ctor_set(v_reuseFailAlloc_2023_, 8, v_snapshotTasks_1996_);
v___x_2017_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = lean_st_ref_set(v___y_1979_, v___x_2017_);
v___x_2019_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2019_);
v___x_2021_ = v___x_1985_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___boxed(lean_object* v_cls_2028_, lean_object* v_msg_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3(v_cls_2028_, v_msg_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2035_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_2049_, lean_object* v_goal_2050_, lean_object* v_target_2051_, uint8_t v_symm_2052_, uint8_t v_side_2053_, lean_object* v_lem_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_fst_2092_; uint8_t v_snd_2093_; uint8_t v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; uint8_t v___y_2164_; lean_object* v___y_2176_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v_val_2274_; 
if (lean_obj_tag(v_lem_2054_) == 0)
{
lean_object* v_val_2282_; 
v_val_2282_ = lean_ctor_get(v_lem_2054_, 0);
lean_inc(v_val_2282_);
lean_dec_ref(v_lem_2054_);
v_val_2274_ = v_val_2282_;
goto v___jp_2273_;
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2284_; 
v_val_2283_ = lean_ctor_get(v_lem_2054_, 0);
lean_inc(v_val_2283_);
lean_dec_ref(v_lem_2054_);
v___x_2284_ = l_Lean_Meta_saveState___redArg(v___y_2056_, v___y_2058_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2283_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; 
lean_dec(v_a_2285_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
v_val_2274_ = v_a_2287_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_target_2051_);
lean_dec(v_goal_2050_);
lean_dec(v_weight_2049_);
v_a_2288_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2290_ = v___x_2286_;
v_isShared_2291_ = v_isSharedCheck_2317_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2317_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint8_t v___y_2293_; uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Exception_isInterrupt(v_a_2288_);
if (v___x_2315_ == 0)
{
uint8_t v___x_2316_; 
lean_inc(v_a_2288_);
v___x_2316_ = l_Lean_Exception_isRuntime(v_a_2288_);
v___y_2293_ = v___x_2316_;
goto v___jp_2292_;
}
else
{
v___y_2293_ = v___x_2315_;
goto v___jp_2292_;
}
v___jp_2292_:
{
if (v___y_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_del_object(v___x_2290_);
lean_dec(v_a_2288_);
v___x_2294_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2285_, v___y_2056_, v___y_2058_);
lean_dec(v_a_2285_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2303_);
v___x_2296_ = v___x_2294_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v___x_2294_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_box(0);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
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
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_a_2304_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2294_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2294_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v___x_2313_; 
lean_dec(v_a_2285_);
if (v_isShared_2291_ == 0)
{
v___x_2313_ = v___x_2290_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2288_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_val_2283_);
lean_dec_ref(v_target_2051_);
lean_dec(v_goal_2050_);
lean_dec(v_weight_2049_);
v_a_2318_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2284_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2284_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
v___jp_2060_:
{
if (v___y_2065_ == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref(v___y_2061_);
v___x_2066_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2064_, v___y_2063_, v___y_2062_);
lean_dec_ref(v___y_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2075_);
v___x_2068_ = v___x_2066_;
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v___x_2066_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2066_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2066_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; 
lean_dec_ref(v___y_2064_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___y_2061_);
return v___x_2084_;
}
}
v___jp_2085_:
{
lean_object* v___x_2094_; lean_object* v_mctx_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_st_ref_get(v___y_2091_);
v_mctx_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_mctx_2095_);
lean_dec(v___x_2094_);
lean_inc_ref(v_mctx_2095_);
v___x_2096_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2095_, v___y_2088_, v___y_2087_, v___y_2091_, v___y_2086_, v___y_2090_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2107_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2101_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2101_, 0, v_fst_2092_);
lean_ctor_set(v___x_2101_, 1, v_weight_2049_);
lean_ctor_set(v___x_2101_, 2, v___y_2089_);
lean_ctor_set(v___x_2101_, 3, v_mctx_2095_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*4, v_snd_2093_);
v___x_2102_ = lean_unbox(v_a_2097_);
lean_dec(v_a_2097_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*4 + 1, v___x_2102_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_mctx_2095_);
lean_dec_ref(v_fst_2092_);
lean_dec_ref(v___y_2089_);
lean_dec(v_weight_2049_);
v_a_2108_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2096_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2096_);
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
v___jp_2116_:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2119_);
if (lean_obj_tag(v___x_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2127_; lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_val_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2126_, v___y_2122_);
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2130_ = lean_unsigned_to_nat(4u);
v___x_2131_ = l_Lean_Expr_isAppOfArity(v_a_2128_, v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2086_ = v___y_2123_;
v___y_2087_ = v___y_2121_;
v___y_2088_ = v___y_2118_;
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___y_2124_;
v___y_2091_ = v___y_2122_;
v_fst_2092_ = v_a_2128_;
v_snd_2093_ = v___y_2120_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2132_ = lean_unsigned_to_nat(3u);
v___x_2133_ = l_Lean_Expr_getAppNumArgs(v_a_2128_);
v___x_2134_ = lean_nat_sub(v___x_2133_, v___x_2132_);
lean_dec(v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_sub(v___x_2134_, v___x_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = l_Lean_Expr_getRevArg_x21(v_a_2128_, v___x_2136_);
lean_dec(v_a_2128_);
v___y_2086_ = v___y_2123_;
v___y_2087_ = v___y_2121_;
v___y_2088_ = v___y_2118_;
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___y_2124_;
v___y_2091_ = v___y_2122_;
v_fst_2092_ = v___x_2137_;
v_snd_2093_ = v___y_2117_;
goto v___jp_2085_;
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v___x_2125_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v_weight_2049_);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
v___jp_2140_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
v___jp_2143_:
{
if (v___y_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref(v___y_2147_);
v___x_2149_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2146_, v___y_2145_, v___y_2144_);
lean_dec_ref(v___y_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_dec_ref(v___x_2149_);
goto v___jp_2140_;
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2158_; 
lean_dec_ref(v___y_2146_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___y_2147_);
return v___x_2158_;
}
}
v___jp_2159_:
{
if (v___y_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref(v___y_2160_);
v___x_2165_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2162_, v___y_2163_, v___y_2161_);
lean_dec_ref(v___y_2162_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_dec_ref(v___x_2165_);
goto v___jp_2140_;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
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
else
{
lean_object* v___x_2174_; 
lean_dec_ref(v___y_2162_);
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2160_);
return v___x_2174_;
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_saveState___redArg(v___y_2056_, v___y_2058_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v___x_2179_ = 1;
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2176_);
v___x_2181_ = l_Lean_MVarId_rewrite(v_goal_2050_, v_target_2051_, v___y_2176_, v_symm_2052_, v___x_2180_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2178_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2243_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2243_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v_eNew_2186_; lean_object* v_mvarIds_2187_; uint8_t v___x_2188_; 
v_eNew_2186_ = lean_ctor_get(v_a_2182_, 0);
v_mvarIds_2187_ = lean_ctor_get(v_a_2182_, 2);
v___x_2188_ = l_List_isEmpty___redArg(v_mvarIds_2187_);
if (v___x_2188_ == 0)
{
lean_inc_ref(v_eNew_2186_);
lean_del_object(v___x_2184_);
lean_dec_ref(v___y_2176_);
switch(v_side_2053_)
{
case 0:
{
if (v___x_2188_ == 0)
{
lean_dec_ref(v_eNew_2186_);
lean_dec(v_a_2182_);
lean_dec(v_weight_2049_);
goto v___jp_2140_;
}
else
{
v___y_2117_ = v___x_2179_;
v___y_2118_ = v_eNew_2186_;
v___y_2119_ = v_a_2182_;
v___y_2120_ = v___x_2188_;
v___y_2121_ = v___y_2055_;
v___y_2122_ = v___y_2056_;
v___y_2123_ = v___y_2057_;
v___y_2124_ = v___y_2058_;
goto v___jp_2116_;
}
}
case 1:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_Meta_saveState___redArg(v___y_2056_, v___y_2058_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = lean_box(0);
lean_inc(v_mvarIds_2187_);
v___x_2192_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2187_, v___x_2191_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_dec_ref(v___x_2192_);
lean_dec(v_a_2190_);
v___y_2117_ = v___x_2179_;
v___y_2118_ = v_eNew_2186_;
v___y_2119_ = v_a_2182_;
v___y_2120_ = v___x_2188_;
v___y_2121_ = v___y_2055_;
v___y_2122_ = v___y_2056_;
v___y_2123_ = v___y_2057_;
v___y_2124_ = v___y_2058_;
goto v___jp_2116_;
}
else
{
lean_object* v_a_2193_; uint8_t v___x_2194_; 
lean_dec_ref(v_eNew_2186_);
lean_dec(v_a_2182_);
lean_dec(v_weight_2049_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
v___x_2194_ = l_Lean_Exception_isInterrupt(v_a_2193_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
lean_inc(v_a_2193_);
v___x_2195_ = l_Lean_Exception_isRuntime(v_a_2193_);
v___y_2160_ = v_a_2193_;
v___y_2161_ = v___y_2058_;
v___y_2162_ = v_a_2190_;
v___y_2163_ = v___y_2056_;
v___y_2164_ = v___x_2195_;
goto v___jp_2159_;
}
else
{
v___y_2160_ = v_a_2193_;
v___y_2161_ = v___y_2058_;
v___y_2162_ = v_a_2190_;
v___y_2163_ = v___y_2056_;
v___y_2164_ = v___x_2194_;
goto v___jp_2159_;
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_eNew_2186_);
lean_dec(v_a_2182_);
lean_dec(v_weight_2049_);
v_a_2196_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2189_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2189_);
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
default: 
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Meta_saveState___redArg(v___y_2056_, v___y_2058_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2187_);
v___x_2207_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2187_, v___x_2206_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2205_);
v___y_2117_ = v___x_2179_;
v___y_2118_ = v_eNew_2186_;
v___y_2119_ = v_a_2182_;
v___y_2120_ = v___x_2188_;
v___y_2121_ = v___y_2055_;
v___y_2122_ = v___y_2056_;
v___y_2123_ = v___y_2057_;
v___y_2124_ = v___y_2058_;
goto v___jp_2116_;
}
else
{
lean_object* v_a_2208_; uint8_t v___x_2209_; 
lean_dec_ref(v_eNew_2186_);
lean_dec(v_a_2182_);
lean_dec(v_weight_2049_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_Exception_isInterrupt(v_a_2208_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; 
lean_inc(v_a_2208_);
v___x_2210_ = l_Lean_Exception_isRuntime(v_a_2208_);
v___y_2144_ = v___y_2058_;
v___y_2145_ = v___y_2056_;
v___y_2146_ = v_a_2205_;
v___y_2147_ = v_a_2208_;
v___y_2148_ = v___x_2210_;
goto v___jp_2143_;
}
else
{
v___y_2144_ = v___y_2058_;
v___y_2145_ = v___y_2056_;
v___y_2146_ = v_a_2205_;
v___y_2147_ = v_a_2208_;
v___y_2148_ = v___x_2209_;
goto v___jp_2143_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v_eNew_2186_);
lean_dec(v_a_2182_);
lean_dec(v_weight_2049_);
v_a_2211_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2204_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2204_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v_mctx_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_st_ref_get(v___y_2056_);
v_mctx_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc_ref(v_mctx_2220_);
lean_dec(v___x_2219_);
lean_inc_ref(v_eNew_2186_);
lean_inc_ref(v_mctx_2220_);
v___x_2221_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2220_, v_eNew_2186_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2234_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2234_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2234_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2229_; 
v___x_2226_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2226_, 0, v___y_2176_);
lean_ctor_set(v___x_2226_, 1, v_weight_2049_);
lean_ctor_set(v___x_2226_, 2, v_a_2182_);
lean_ctor_set(v___x_2226_, 3, v_mctx_2220_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*4, v_symm_2052_);
v___x_2227_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*4 + 1, v___x_2227_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set_tag(v___x_2184_, 1);
lean_ctor_set(v___x_2184_, 0, v___x_2226_);
v___x_2229_ = v___x_2184_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2226_);
v___x_2229_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_mctx_2220_);
lean_del_object(v___x_2184_);
lean_dec(v_a_2182_);
lean_dec_ref(v___y_2176_);
lean_dec(v_weight_2049_);
v_a_2235_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2221_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2221_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
else
{
lean_object* v_a_2244_; uint8_t v___x_2245_; 
lean_dec_ref(v___y_2176_);
lean_dec(v_weight_2049_);
v_a_2244_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2181_);
v___x_2245_ = l_Lean_Exception_isInterrupt(v_a_2244_);
if (v___x_2245_ == 0)
{
uint8_t v___x_2246_; 
lean_inc(v_a_2244_);
v___x_2246_ = l_Lean_Exception_isRuntime(v_a_2244_);
v___y_2061_ = v_a_2244_;
v___y_2062_ = v___y_2058_;
v___y_2063_ = v___y_2056_;
v___y_2064_ = v_a_2178_;
v___y_2065_ = v___x_2246_;
goto v___jp_2060_;
}
else
{
v___y_2061_ = v_a_2244_;
v___y_2062_ = v___y_2058_;
v___y_2063_ = v___y_2056_;
v___y_2064_ = v_a_2178_;
v___y_2065_ = v___x_2245_;
goto v___jp_2060_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_target_2051_);
lean_dec(v_goal_2050_);
lean_dec(v_weight_2049_);
v_a_2247_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2177_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2177_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2260_ = l_Lean_stringToMessageData(v___y_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___y_2257_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
lean_inc_ref(v___y_2258_);
v___x_2262_ = l_Lean_MessageData_ofExpr(v___y_2258_);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3(v___y_2256_, v___x_2263_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_dec_ref(v___x_2264_);
v___y_2176_ = v___y_2258_;
goto v___jp_2175_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_target_2051_);
lean_dec(v_goal_2050_);
lean_dec(v_weight_2049_);
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v_a_2277_; uint8_t v___x_2278_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2276_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(v___x_2275_, v___y_2057_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_unbox(v_a_2277_);
lean_dec(v_a_2277_);
if (v___x_2278_ == 0)
{
v___y_2176_ = v_val_2274_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4);
if (v_symm_2052_ == 0)
{
lean_object* v___x_2280_; 
v___x_2280_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3___closed__1));
v___y_2256_ = v___x_2275_;
v___y_2257_ = v___x_2279_;
v___y_2258_ = v_val_2274_;
v___y_2259_ = v___x_2280_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2281_; 
v___x_2281_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5));
v___y_2256_ = v___x_2275_;
v___y_2257_ = v___x_2279_;
v___y_2258_ = v_val_2274_;
v___y_2259_ = v___x_2281_;
goto v___jp_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2326_, lean_object* v_goal_2327_, lean_object* v_target_2328_, lean_object* v_symm_2329_, lean_object* v_side_2330_, lean_object* v_lem_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_symm_boxed_2337_; uint8_t v_side_boxed_2338_; lean_object* v_res_2339_; 
v_symm_boxed_2337_ = lean_unbox(v_symm_2329_);
v_side_boxed_2338_ = lean_unbox(v_side_2330_);
v_res_2339_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2326_, v_goal_2327_, v_target_2328_, v_symm_boxed_2337_, v_side_boxed_2338_, v_lem_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2340_, lean_object* v_goal_2341_, lean_object* v_target_2342_, uint8_t v_side_2343_, lean_object* v_lem_2344_, uint8_t v_symm_2345_, lean_object* v_weight_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; 
v___x_2352_ = lean_box(v_symm_2345_);
v___x_2353_ = lean_box(v_side_2343_);
v___f_2354_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2354_, 0, v_weight_2346_);
lean_closure_set(v___f_2354_, 1, v_goal_2341_);
lean_closure_set(v___f_2354_, 2, v_target_2342_);
lean_closure_set(v___f_2354_, 3, v___x_2352_);
lean_closure_set(v___f_2354_, 4, v___x_2353_);
lean_closure_set(v___f_2354_, 5, v_lem_2344_);
v___x_2355_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2340_, v___f_2354_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2356_, lean_object* v_goal_2357_, lean_object* v_target_2358_, lean_object* v_side_2359_, lean_object* v_lem_2360_, lean_object* v_symm_2361_, lean_object* v_weight_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
uint8_t v_side_boxed_2368_; uint8_t v_symm_boxed_2369_; lean_object* v_res_2370_; 
v_side_boxed_2368_ = lean_unbox(v_side_2359_);
v_symm_boxed_2369_ = lean_unbox(v_symm_2361_);
v_res_2370_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2356_, v_goal_2357_, v_target_2358_, v_side_boxed_2368_, v_lem_2360_, v_symm_boxed_2369_, v_weight_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2371_, lean_object* v_k_2372_, uint8_t v_cleanupAnnotations_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___f_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2379_, 0, v_k_2372_);
v___x_2380_ = 0;
v___x_2381_ = lean_box(0);
v___x_2382_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2380_, v___x_2381_, v_type_2371_, v___f_2379_, v_cleanupAnnotations_2373_, v___x_2380_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_a_2391_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2382_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2382_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2399_, lean_object* v_k_2400_, lean_object* v_cleanupAnnotations_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2407_; lean_object* v_res_2408_; 
v_cleanupAnnotations_boxed_2407_ = lean_unbox(v_cleanupAnnotations_2401_);
v_res_2408_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2399_, v_k_2400_, v_cleanupAnnotations_boxed_2407_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2409_, lean_object* v_type_2410_, lean_object* v_k_2411_, uint8_t v_cleanupAnnotations_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2410_, v_k_2411_, v_cleanupAnnotations_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_type_2420_, lean_object* v_k_2421_, lean_object* v_cleanupAnnotations_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2428_; lean_object* v_res_2429_; 
v_cleanupAnnotations_boxed_2428_ = lean_unbox(v_cleanupAnnotations_2422_);
v_res_2429_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2419_, v_type_2420_, v_k_2421_, v_cleanupAnnotations_boxed_2428_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2430_, lean_object* v_k_2431_, uint8_t v_cleanupAnnotations_2432_, uint8_t v_preserveNondepLet_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___f_2439_; uint8_t v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2439_, 0, v_k_2431_);
v___x_2440_ = 1;
v___x_2441_ = 0;
v___x_2442_ = lean_box(0);
v___x_2443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2430_, v___x_2440_, v___x_2440_, v_preserveNondepLet_2433_, v___x_2441_, v___x_2442_, v___f_2439_, v_cleanupAnnotations_2432_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2443_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2443_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2460_, lean_object* v_k_2461_, lean_object* v_cleanupAnnotations_2462_, lean_object* v_preserveNondepLet_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2469_; uint8_t v_preserveNondepLet_boxed_2470_; lean_object* v_res_2471_; 
v_cleanupAnnotations_boxed_2469_ = lean_unbox(v_cleanupAnnotations_2462_);
v_preserveNondepLet_boxed_2470_ = lean_unbox(v_preserveNondepLet_2463_);
v_res_2471_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2460_, v_k_2461_, v_cleanupAnnotations_boxed_2469_, v_preserveNondepLet_boxed_2470_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2472_, lean_object* v_e_2473_, lean_object* v_k_2474_, uint8_t v_cleanupAnnotations_2475_, uint8_t v_preserveNondepLet_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2473_, v_k_2474_, v_cleanupAnnotations_2475_, v_preserveNondepLet_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_e_2484_, lean_object* v_k_2485_, lean_object* v_cleanupAnnotations_2486_, lean_object* v_preserveNondepLet_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2493_; uint8_t v_preserveNondepLet_boxed_2494_; lean_object* v_res_2495_; 
v_cleanupAnnotations_boxed_2493_ = lean_unbox(v_cleanupAnnotations_2486_);
v_preserveNondepLet_boxed_2494_ = lean_unbox(v_preserveNondepLet_2487_);
v_res_2495_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2483_, v_e_2484_, v_k_2485_, v_cleanupAnnotations_boxed_2493_, v_preserveNondepLet_boxed_2494_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2496_, lean_object* v_e_x27_2497_, lean_object* v_a_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
lean_inc_ref(v_e_x27_2497_);
v___x_2504_ = lean_apply_7(v_f_2496_, v_a_2498_, v_e_x27_2497_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2513_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_e_x27_2497_);
lean_ctor_set(v___x_2509_, 1, v_a_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2509_);
v___x_2511_ = v___x_2507_;
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
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_e_x27_2497_);
v_a_2514_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2504_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2504_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2522_, lean_object* v_e_x27_2523_, lean_object* v_a_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2522_, v_e_x27_2523_, v_a_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2531_, lean_object* v_x_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
switch(lean_obj_tag(v_x_2532_))
{
case 7:
{
lean_object* v_binderName_2539_; lean_object* v_binderType_2540_; lean_object* v_body_2541_; uint8_t v_binderInfo_2542_; lean_object* v___x_2543_; 
v_binderName_2539_ = lean_ctor_get(v_x_2532_, 0);
v_binderType_2540_ = lean_ctor_get(v_x_2532_, 1);
v_body_2541_ = lean_ctor_get(v_x_2532_, 2);
v_binderInfo_2542_ = lean_ctor_get_uint8(v_x_2532_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2540_);
lean_inc_ref(v_f_2531_);
v___x_2543_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_binderType_2540_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___x_2547_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v_fst_2545_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_fst_2545_);
v_snd_2546_ = lean_ctor_get(v_a_2544_, 1);
lean_inc(v_snd_2546_);
lean_dec(v_a_2544_);
lean_inc_ref(v_body_2541_);
v___x_2547_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_body_2541_, v_snd_2546_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2577_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2577_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2577_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2576_; 
v_fst_2552_ = lean_ctor_get(v_a_2548_, 0);
v_snd_2553_ = lean_ctor_get(v_a_2548_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_a_2548_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2555_ = v_a_2548_;
v_isShared_2556_ = v_isSharedCheck_2576_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snd_2553_);
lean_inc(v_fst_2552_);
lean_dec(v_a_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2576_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___y_2558_; uint8_t v___y_2566_; size_t v___x_2570_; size_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_ptr_addr(v_binderType_2540_);
v___x_2571_ = lean_ptr_addr(v_fst_2545_);
v___x_2572_ = lean_usize_dec_eq(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
v___y_2566_ = v___x_2572_;
goto v___jp_2565_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = lean_ptr_addr(v_body_2541_);
v___x_2574_ = lean_ptr_addr(v_fst_2552_);
v___x_2575_ = lean_usize_dec_eq(v___x_2573_, v___x_2574_);
v___y_2566_ = v___x_2575_;
goto v___jp_2565_;
}
v___jp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___y_2558_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___y_2558_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_snd_2553_);
v___x_2560_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2562_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2560_);
v___x_2562_ = v___x_2550_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
v___jp_2565_:
{
if (v___y_2566_ == 0)
{
lean_object* v___x_2567_; 
lean_inc(v_binderName_2539_);
lean_dec_ref(v_x_2532_);
v___x_2567_ = l_Lean_Expr_forallE___override(v_binderName_2539_, v_fst_2545_, v_fst_2552_, v_binderInfo_2542_);
v___y_2558_ = v___x_2567_;
goto v___jp_2557_;
}
else
{
uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2542_, v_binderInfo_2542_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_inc(v_binderName_2539_);
lean_dec_ref(v_x_2532_);
v___x_2569_ = l_Lean_Expr_forallE___override(v_binderName_2539_, v_fst_2545_, v_fst_2552_, v_binderInfo_2542_);
v___y_2558_ = v___x_2569_;
goto v___jp_2557_;
}
else
{
lean_dec(v_fst_2552_);
lean_dec(v_fst_2545_);
v___y_2558_ = v_x_2532_;
goto v___jp_2557_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2545_);
lean_dec_ref(v_x_2532_);
return v___x_2547_;
}
}
else
{
lean_dec_ref(v_x_2532_);
lean_dec_ref(v_f_2531_);
return v___x_2543_;
}
}
case 6:
{
lean_object* v_binderName_2578_; lean_object* v_binderType_2579_; lean_object* v_body_2580_; uint8_t v_binderInfo_2581_; lean_object* v___x_2582_; 
v_binderName_2578_ = lean_ctor_get(v_x_2532_, 0);
v_binderType_2579_ = lean_ctor_get(v_x_2532_, 1);
v_body_2580_ = lean_ctor_get(v_x_2532_, 2);
v_binderInfo_2581_ = lean_ctor_get_uint8(v_x_2532_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2579_);
lean_inc_ref(v_f_2531_);
v___x_2582_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_binderType_2579_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v_fst_2584_; lean_object* v_snd_2585_; lean_object* v___x_2586_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
v_fst_2584_ = lean_ctor_get(v_a_2583_, 0);
lean_inc(v_fst_2584_);
v_snd_2585_ = lean_ctor_get(v_a_2583_, 1);
lean_inc(v_snd_2585_);
lean_dec(v_a_2583_);
lean_inc_ref(v_body_2580_);
v___x_2586_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_body_2580_, v_snd_2585_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2616_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2616_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2616_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_fst_2591_; lean_object* v_snd_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2615_; 
v_fst_2591_ = lean_ctor_get(v_a_2587_, 0);
v_snd_2592_ = lean_ctor_get(v_a_2587_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2594_ = v_a_2587_;
v_isShared_2595_ = v_isSharedCheck_2615_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_snd_2592_);
lean_inc(v_fst_2591_);
lean_dec(v_a_2587_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2615_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___y_2597_; uint8_t v___y_2605_; size_t v___x_2609_; size_t v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = lean_ptr_addr(v_binderType_2579_);
v___x_2610_ = lean_ptr_addr(v_fst_2584_);
v___x_2611_ = lean_usize_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
v___y_2605_ = v___x_2611_;
goto v___jp_2604_;
}
else
{
size_t v___x_2612_; size_t v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = lean_ptr_addr(v_body_2580_);
v___x_2613_ = lean_ptr_addr(v_fst_2591_);
v___x_2614_ = lean_usize_dec_eq(v___x_2612_, v___x_2613_);
v___y_2605_ = v___x_2614_;
goto v___jp_2604_;
}
v___jp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___y_2597_);
v___x_2599_ = v___x_2594_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___y_2597_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_snd_2592_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2601_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2599_);
v___x_2601_ = v___x_2589_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
v___jp_2604_:
{
if (v___y_2605_ == 0)
{
lean_object* v___x_2606_; 
lean_inc(v_binderName_2578_);
lean_dec_ref(v_x_2532_);
v___x_2606_ = l_Lean_Expr_lam___override(v_binderName_2578_, v_fst_2584_, v_fst_2591_, v_binderInfo_2581_);
v___y_2597_ = v___x_2606_;
goto v___jp_2596_;
}
else
{
uint8_t v___x_2607_; 
v___x_2607_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2581_, v_binderInfo_2581_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_inc(v_binderName_2578_);
lean_dec_ref(v_x_2532_);
v___x_2608_ = l_Lean_Expr_lam___override(v_binderName_2578_, v_fst_2584_, v_fst_2591_, v_binderInfo_2581_);
v___y_2597_ = v___x_2608_;
goto v___jp_2596_;
}
else
{
lean_dec(v_fst_2591_);
lean_dec(v_fst_2584_);
v___y_2597_ = v_x_2532_;
goto v___jp_2596_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2584_);
lean_dec_ref(v_x_2532_);
return v___x_2586_;
}
}
else
{
lean_dec_ref(v_x_2532_);
lean_dec_ref(v_f_2531_);
return v___x_2582_;
}
}
case 10:
{
lean_object* v_data_2617_; lean_object* v_expr_2618_; lean_object* v___x_2619_; 
v_data_2617_ = lean_ctor_get(v_x_2532_, 0);
v_expr_2618_ = lean_ctor_get(v_x_2532_, 1);
lean_inc_ref(v_expr_2618_);
v___x_2619_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_expr_2618_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2642_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2642_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2642_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v_fst_2624_; lean_object* v_snd_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2641_; 
v_fst_2624_ = lean_ctor_get(v_a_2620_, 0);
v_snd_2625_ = lean_ctor_get(v_a_2620_, 1);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2627_ = v_a_2620_;
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_snd_2625_);
lean_inc(v_fst_2624_);
lean_dec(v_a_2620_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___y_2630_; size_t v___x_2637_; size_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2637_ = lean_ptr_addr(v_expr_2618_);
v___x_2638_ = lean_ptr_addr(v_fst_2624_);
v___x_2639_ = lean_usize_dec_eq(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_inc(v_data_2617_);
lean_dec_ref(v_x_2532_);
v___x_2640_ = l_Lean_Expr_mdata___override(v_data_2617_, v_fst_2624_);
v___y_2630_ = v___x_2640_;
goto v___jp_2629_;
}
else
{
lean_dec(v_fst_2624_);
v___y_2630_ = v_x_2532_;
goto v___jp_2629_;
}
v___jp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___y_2630_);
v___x_2632_ = v___x_2627_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___y_2630_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_snd_2625_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2632_);
v___x_2634_ = v___x_2622_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_2532_);
return v___x_2619_;
}
}
case 8:
{
lean_object* v_declName_2643_; lean_object* v_type_2644_; lean_object* v_value_2645_; lean_object* v_body_2646_; uint8_t v_nondep_2647_; lean_object* v___x_2648_; 
v_declName_2643_ = lean_ctor_get(v_x_2532_, 0);
v_type_2644_ = lean_ctor_get(v_x_2532_, 1);
v_value_2645_ = lean_ctor_get(v_x_2532_, 2);
v_body_2646_ = lean_ctor_get(v_x_2532_, 3);
v_nondep_2647_ = lean_ctor_get_uint8(v_x_2532_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2644_);
lean_inc_ref(v_f_2531_);
v___x_2648_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_type_2644_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_fst_2650_; lean_object* v_snd_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v_fst_2650_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_fst_2650_);
v_snd_2651_ = lean_ctor_get(v_a_2649_, 1);
lean_inc(v_snd_2651_);
lean_dec(v_a_2649_);
lean_inc_ref(v_value_2645_);
lean_inc_ref(v_f_2531_);
v___x_2652_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_value_2645_, v_snd_2651_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2656_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v_fst_2654_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_fst_2654_);
v_snd_2655_ = lean_ctor_get(v_a_2653_, 1);
lean_inc(v_snd_2655_);
lean_dec(v_a_2653_);
lean_inc_ref(v_body_2646_);
v___x_2656_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_body_2646_, v_snd_2655_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2688_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2688_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2688_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2687_; 
v_fst_2661_ = lean_ctor_get(v_a_2657_, 0);
v_snd_2662_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2664_ = v_a_2657_;
v_isShared_2665_ = v_isSharedCheck_2687_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2662_);
lean_inc(v_fst_2661_);
lean_dec(v_a_2657_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2687_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___y_2667_; uint8_t v___y_2675_; size_t v___x_2681_; size_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2681_ = lean_ptr_addr(v_type_2644_);
v___x_2682_ = lean_ptr_addr(v_fst_2650_);
v___x_2683_ = lean_usize_dec_eq(v___x_2681_, v___x_2682_);
if (v___x_2683_ == 0)
{
v___y_2675_ = v___x_2683_;
goto v___jp_2674_;
}
else
{
size_t v___x_2684_; size_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2684_ = lean_ptr_addr(v_value_2645_);
v___x_2685_ = lean_ptr_addr(v_fst_2654_);
v___x_2686_ = lean_usize_dec_eq(v___x_2684_, v___x_2685_);
v___y_2675_ = v___x_2686_;
goto v___jp_2674_;
}
v___jp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___y_2667_);
v___x_2669_ = v___x_2664_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___y_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_snd_2662_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2669_);
v___x_2671_ = v___x_2659_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
v___jp_2674_:
{
if (v___y_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_inc(v_declName_2643_);
lean_dec_ref(v_x_2532_);
v___x_2676_ = l_Lean_Expr_letE___override(v_declName_2643_, v_fst_2650_, v_fst_2654_, v_fst_2661_, v_nondep_2647_);
v___y_2667_ = v___x_2676_;
goto v___jp_2666_;
}
else
{
size_t v___x_2677_; size_t v___x_2678_; uint8_t v___x_2679_; 
v___x_2677_ = lean_ptr_addr(v_body_2646_);
v___x_2678_ = lean_ptr_addr(v_fst_2661_);
v___x_2679_ = lean_usize_dec_eq(v___x_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_inc(v_declName_2643_);
lean_dec_ref(v_x_2532_);
v___x_2680_ = l_Lean_Expr_letE___override(v_declName_2643_, v_fst_2650_, v_fst_2654_, v_fst_2661_, v_nondep_2647_);
v___y_2667_ = v___x_2680_;
goto v___jp_2666_;
}
else
{
lean_dec(v_fst_2661_);
lean_dec(v_fst_2654_);
lean_dec(v_fst_2650_);
v___y_2667_ = v_x_2532_;
goto v___jp_2666_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2654_);
lean_dec(v_fst_2650_);
lean_dec_ref(v_x_2532_);
return v___x_2656_;
}
}
else
{
lean_dec(v_fst_2650_);
lean_dec_ref(v_x_2532_);
lean_dec_ref(v_f_2531_);
return v___x_2652_;
}
}
else
{
lean_dec_ref(v_x_2532_);
lean_dec_ref(v_f_2531_);
return v___x_2648_;
}
}
case 5:
{
lean_object* v_fn_2689_; lean_object* v_arg_2690_; lean_object* v___x_2691_; 
v_fn_2689_ = lean_ctor_get(v_x_2532_, 0);
v_arg_2690_ = lean_ctor_get(v_x_2532_, 1);
lean_inc_ref(v_fn_2689_);
lean_inc_ref(v_f_2531_);
v___x_2691_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_fn_2689_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2695_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v_fst_2693_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_fst_2693_);
v_snd_2694_ = lean_ctor_get(v_a_2692_, 1);
lean_inc(v_snd_2694_);
lean_dec(v_a_2692_);
lean_inc_ref(v_arg_2690_);
v___x_2695_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_arg_2690_, v_snd_2694_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2723_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2723_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2723_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_fst_2700_; lean_object* v_snd_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2722_; 
v_fst_2700_ = lean_ctor_get(v_a_2696_, 0);
v_snd_2701_ = lean_ctor_get(v_a_2696_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_a_2696_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2703_ = v_a_2696_;
v_isShared_2704_ = v_isSharedCheck_2722_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_snd_2701_);
lean_inc(v_fst_2700_);
lean_dec(v_a_2696_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2722_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___y_2706_; uint8_t v___y_2714_; size_t v___x_2716_; size_t v___x_2717_; uint8_t v___x_2718_; 
v___x_2716_ = lean_ptr_addr(v_fn_2689_);
v___x_2717_ = lean_ptr_addr(v_fst_2693_);
v___x_2718_ = lean_usize_dec_eq(v___x_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
v___y_2714_ = v___x_2718_;
goto v___jp_2713_;
}
else
{
size_t v___x_2719_; size_t v___x_2720_; uint8_t v___x_2721_; 
v___x_2719_ = lean_ptr_addr(v_arg_2690_);
v___x_2720_ = lean_ptr_addr(v_fst_2700_);
v___x_2721_ = lean_usize_dec_eq(v___x_2719_, v___x_2720_);
v___y_2714_ = v___x_2721_;
goto v___jp_2713_;
}
v___jp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___y_2706_);
v___x_2708_ = v___x_2703_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___y_2706_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_snd_2701_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2708_);
v___x_2710_ = v___x_2698_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
v___jp_2713_:
{
if (v___y_2714_ == 0)
{
lean_object* v___x_2715_; 
lean_dec_ref(v_x_2532_);
v___x_2715_ = l_Lean_Expr_app___override(v_fst_2693_, v_fst_2700_);
v___y_2706_ = v___x_2715_;
goto v___jp_2705_;
}
else
{
lean_dec(v_fst_2700_);
lean_dec(v_fst_2693_);
v___y_2706_ = v_x_2532_;
goto v___jp_2705_;
}
}
}
}
}
else
{
lean_dec(v_fst_2693_);
lean_dec_ref(v_x_2532_);
return v___x_2695_;
}
}
else
{
lean_dec_ref(v_x_2532_);
lean_dec_ref(v_f_2531_);
return v___x_2691_;
}
}
case 11:
{
lean_object* v_typeName_2724_; lean_object* v_idx_2725_; lean_object* v_struct_2726_; lean_object* v___x_2727_; 
v_typeName_2724_ = lean_ctor_get(v_x_2532_, 0);
v_idx_2725_ = lean_ctor_get(v_x_2532_, 1);
v_struct_2726_ = lean_ctor_get(v_x_2532_, 2);
lean_inc_ref(v_struct_2726_);
v___x_2727_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2531_, v_struct_2726_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2750_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2750_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2750_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_fst_2732_; lean_object* v_snd_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2749_; 
v_fst_2732_ = lean_ctor_get(v_a_2728_, 0);
v_snd_2733_ = lean_ctor_get(v_a_2728_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_a_2728_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2735_ = v_a_2728_;
v_isShared_2736_ = v_isSharedCheck_2749_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_snd_2733_);
lean_inc(v_fst_2732_);
lean_dec(v_a_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2749_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___y_2738_; size_t v___x_2745_; size_t v___x_2746_; uint8_t v___x_2747_; 
v___x_2745_ = lean_ptr_addr(v_struct_2726_);
v___x_2746_ = lean_ptr_addr(v_fst_2732_);
v___x_2747_ = lean_usize_dec_eq(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; 
lean_inc(v_idx_2725_);
lean_inc(v_typeName_2724_);
lean_dec_ref(v_x_2532_);
v___x_2748_ = l_Lean_Expr_proj___override(v_typeName_2724_, v_idx_2725_, v_fst_2732_);
v___y_2738_ = v___x_2748_;
goto v___jp_2737_;
}
else
{
lean_dec(v_fst_2732_);
v___y_2738_ = v_x_2532_;
goto v___jp_2737_;
}
v___jp_2737_:
{
lean_object* v___x_2740_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___y_2738_);
v___x_2740_ = v___x_2735_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___y_2738_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_snd_2733_);
v___x_2740_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2742_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2740_);
v___x_2742_ = v___x_2730_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
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
}
else
{
lean_dec_ref(v_x_2532_);
return v___x_2727_;
}
}
default: 
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec_ref(v_f_2531_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_x_2532_);
lean_ctor_set(v___x_2751_, 1, v___y_2533_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2753_, lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2753_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2762_, lean_object* v_init_2763_, lean_object* v_e_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2762_, v_e_2764_, v_init_2763_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_snd_2775_; lean_object* v___x_2777_; 
v_snd_2775_ = lean_ctor_get(v_a_2771_, 1);
lean_inc(v_snd_2775_);
lean_dec(v_a_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_snd_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_snd_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_a_2780_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2770_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2770_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2788_, lean_object* v_init_2789_, lean_object* v_e_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2788_, v_init_2789_, v_e_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2799_, lean_object* v_as_2800_, size_t v_i_2801_, size_t v_stop_2802_, lean_object* v_b_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_a_2810_; uint8_t v___x_2814_; 
v___x_2814_ = lean_usize_dec_eq(v_i_2801_, v_stop_2802_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_array_uget_borrowed(v_as_2800_, v_i_2801_);
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
lean_inc(v___x_2815_);
v___x_2816_ = lean_infer_type(v___x_2815_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
lean_inc_ref(v_op_2799_);
v___x_2818_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2799_, v_a_2817_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = l_Array_append___redArg(v_b_2803_, v_a_2819_);
lean_dec(v_a_2819_);
v_a_2810_ = v___x_2820_;
goto v___jp_2809_;
}
else
{
lean_dec_ref(v_b_2803_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2818_);
v_a_2810_ = v_a_2821_;
goto v___jp_2809_;
}
else
{
lean_dec_ref(v_op_2799_);
return v___x_2818_;
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v_b_2803_);
lean_dec_ref(v_op_2799_);
v_a_2822_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2816_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2816_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v___x_2830_; 
lean_dec_ref(v_op_2799_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_b_2803_);
return v___x_2830_;
}
v___jp_2809_:
{
size_t v___x_2811_; size_t v___x_2812_; 
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2801_, v___x_2811_);
v_i_2801_ = v___x_2812_;
v_b_2803_ = v_a_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2831_, lean_object* v_args_2832_, lean_object* v_body_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
lean_inc_ref(v_op_2831_);
v___x_2839_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2831_, v_body_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2861_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2861_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2861_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2844_ = l_Array_reverse___redArg(v_a_2840_);
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_array_get_size(v_args_2832_);
v___x_2847_ = lean_nat_dec_lt(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v_op_2831_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2844_);
v___x_2849_ = v___x_2842_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_nat_dec_le(v___x_2846_, v___x_2846_);
if (v___x_2851_ == 0)
{
if (v___x_2847_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v_op_2831_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2844_);
v___x_2853_ = v___x_2842_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2844_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
lean_del_object(v___x_2842_);
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2846_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2831_, v_args_2832_, v___x_2855_, v___x_2856_, v___x_2844_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2857_;
}
}
else
{
size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
lean_del_object(v___x_2842_);
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = lean_usize_of_nat(v___x_2846_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2831_, v_args_2832_, v___x_2858_, v___x_2859_, v___x_2844_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2860_;
}
}
}
}
else
{
lean_dec_ref(v_op_2831_);
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2862_, lean_object* v_args_2863_, lean_object* v_body_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2862_, v_args_2863_, v_body_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_args_2863_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2871_, lean_object* v_a_2872_, lean_object* v_f_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2871_, v_a_2872_, v_f_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2880_, lean_object* v_e_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
switch(lean_obj_tag(v_e_2881_))
{
case 0:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec_ref(v_e_2881_);
lean_dec_ref(v_op_2880_);
v___x_2887_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
case 7:
{
lean_object* v___f_2889_; uint8_t v___x_2890_; lean_object* v___x_2891_; 
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2889_, 0, v_op_2880_);
v___x_2890_ = 0;
v___x_2891_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2881_, v___f_2889_, v___x_2890_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2891_;
}
case 6:
{
lean_object* v___f_2892_; uint8_t v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; 
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2892_, 0, v_op_2880_);
v___x_2893_ = 0;
v___x_2894_ = 1;
v___x_2895_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2881_, v___f_2892_, v___x_2893_, v___x_2894_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2895_;
}
case 8:
{
lean_object* v___f_2896_; uint8_t v___x_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; 
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2896_, 0, v_op_2880_);
v___x_2897_ = 0;
v___x_2898_ = 1;
v___x_2899_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2881_, v___f_2896_, v___x_2897_, v___x_2898_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2899_;
}
default: 
{
lean_object* v___x_2900_; 
lean_inc_ref(v_op_2880_);
lean_inc(v_a_2885_);
lean_inc_ref(v_a_2884_);
lean_inc(v_a_2883_);
lean_inc_ref(v_a_2882_);
lean_inc_ref(v_e_2881_);
v___x_2900_ = lean_apply_6(v_op_2880_, v_e_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, lean_box(0));
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref(v___x_2900_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2902_, 0, v_op_2880_);
v___x_2903_ = l_Array_reverse___redArg(v_a_2901_);
v___x_2904_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2902_, v___x_2903_, v_e_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2904_;
}
else
{
lean_dec_ref(v_e_2881_);
lean_dec_ref(v_op_2880_);
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2905_, lean_object* v_a_2906_, lean_object* v_f_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2905_, v_f_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = l_Array_append___redArg(v_a_2906_, v_a_2914_);
lean_dec(v_a_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_dec_ref(v_a_2906_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2923_, lean_object* v_as_2924_, lean_object* v_i_2925_, lean_object* v_stop_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
size_t v_i_boxed_2933_; size_t v_stop_boxed_2934_; lean_object* v_res_2935_; 
v_i_boxed_2933_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_stop_boxed_2934_ = lean_unbox_usize(v_stop_2926_);
lean_dec(v_stop_2926_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2923_, v_as_2924_, v_i_boxed_2933_, v_stop_boxed_2934_, v_b_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_as_2924_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2936_, lean_object* v_e_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2936_, v_e_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2944_, lean_object* v_op_2945_, lean_object* v_e_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2945_, v_e_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2953_, lean_object* v_op_2954_, lean_object* v_e_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2953_, v_op_2954_, v_e_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2962_, lean_object* v_op_2963_, lean_object* v_as_2964_, size_t v_i_2965_, size_t v_stop_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2963_, v_as_2964_, v_i_2965_, v_stop_2966_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2974_, lean_object* v_op_2975_, lean_object* v_as_2976_, lean_object* v_i_2977_, lean_object* v_stop_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
size_t v_i_boxed_2985_; size_t v_stop_boxed_2986_; lean_object* v_res_2987_; 
v_i_boxed_2985_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_stop_boxed_2986_ = lean_unbox_usize(v_stop_2978_);
lean_dec(v_stop_2978_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2974_, v_op_2975_, v_as_2976_, v_i_boxed_2985_, v_stop_boxed_2986_, v_b_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v_as_2976_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2988_, lean_object* v_f_2989_, lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2989_, v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2998_, lean_object* v_f_2999_, lean_object* v_x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2998_, v_f_2999_, v_x_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_3008_, lean_object* v_f_3009_, lean_object* v_init_3010_, lean_object* v_e_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_3009_, v_init_3010_, v_e_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_f_3019_, lean_object* v_init_3020_, lean_object* v_e_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_3018_, v_f_3019_, v_init_3020_, v_e_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_3028_, size_t v_i_3029_, lean_object* v_bs_3030_){
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
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_3049_, lean_object* v_i_3050_, lean_object* v_bs_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3049_);
lean_dec(v_sz_3049_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3050_);
lean_dec(v_i_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_3052_, v_i_boxed_3053_, v_bs_3051_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3055_, lean_object* v_j_3056_){
_start:
{
lean_object* v_zero_3057_; uint8_t v_isZero_3058_; 
v_zero_3057_ = lean_unsigned_to_nat(0u);
v_isZero_3058_ = lean_nat_dec_eq(v_j_3056_, v_zero_3057_);
if (v_isZero_3058_ == 1)
{
lean_dec(v_j_3056_);
return v_xs_3055_;
}
else
{
lean_object* v___x_3059_; lean_object* v_snd_3060_; lean_object* v_snd_3061_; lean_object* v_one_3062_; lean_object* v_n_3063_; lean_object* v___x_3064_; lean_object* v_snd_3065_; lean_object* v_snd_3066_; uint8_t v___x_3067_; 
v___x_3059_ = lean_array_fget_borrowed(v_xs_3055_, v_j_3056_);
v_snd_3060_ = lean_ctor_get(v___x_3059_, 1);
v_snd_3061_ = lean_ctor_get(v_snd_3060_, 1);
v_one_3062_ = lean_unsigned_to_nat(1u);
v_n_3063_ = lean_nat_sub(v_j_3056_, v_one_3062_);
v___x_3064_ = lean_array_fget_borrowed(v_xs_3055_, v_n_3063_);
v_snd_3065_ = lean_ctor_get(v___x_3064_, 1);
v_snd_3066_ = lean_ctor_get(v_snd_3065_, 1);
v___x_3067_ = lean_nat_dec_lt(v_snd_3066_, v_snd_3061_);
if (v___x_3067_ == 0)
{
lean_dec(v_n_3063_);
lean_dec(v_j_3056_);
return v_xs_3055_;
}
else
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_array_fswap(v_xs_3055_, v_j_3056_, v_n_3063_);
lean_dec(v_j_3056_);
v_xs_3055_ = v___x_3068_;
v_j_3056_ = v_n_3063_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3070_, lean_object* v_i_3071_, lean_object* v_fuel_3072_){
_start:
{
lean_object* v_zero_3073_; uint8_t v_isZero_3074_; 
v_zero_3073_ = lean_unsigned_to_nat(0u);
v_isZero_3074_ = lean_nat_dec_eq(v_fuel_3072_, v_zero_3073_);
if (v_isZero_3074_ == 1)
{
lean_dec(v_fuel_3072_);
lean_dec(v_i_3071_);
return v_xs_3070_;
}
else
{
lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = lean_array_get_size(v_xs_3070_);
v___x_3076_ = lean_nat_dec_lt(v_i_3071_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_dec(v_fuel_3072_);
lean_dec(v_i_3071_);
return v_xs_3070_;
}
else
{
lean_object* v_one_3077_; lean_object* v_n_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_one_3077_ = lean_unsigned_to_nat(1u);
v_n_3078_ = lean_nat_sub(v_fuel_3072_, v_one_3077_);
lean_dec(v_fuel_3072_);
lean_inc(v_i_3071_);
v___x_3079_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3070_, v_i_3071_);
v___x_3080_ = lean_nat_add(v_i_3071_, v_one_3077_);
lean_dec(v_i_3071_);
v_xs_3070_ = v___x_3079_;
v_i_3071_ = v___x_3080_;
v_fuel_3072_ = v_n_3078_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3082_, size_t v_i_3083_, lean_object* v_bs_3084_){
_start:
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_usize_dec_lt(v_i_3083_, v_sz_3082_);
if (v___x_3085_ == 0)
{
return v_bs_3084_;
}
else
{
lean_object* v_v_3086_; lean_object* v_fst_3087_; lean_object* v_snd_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3102_; 
v_v_3086_ = lean_array_uget(v_bs_3084_, v_i_3083_);
v_fst_3087_ = lean_ctor_get(v_v_3086_, 0);
v_snd_3088_ = lean_ctor_get(v_v_3086_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_v_3086_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3090_ = v_v_3086_;
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_snd_3088_);
lean_inc(v_fst_3087_);
lean_dec(v_v_3086_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v_bs_x27_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3092_ = lean_unsigned_to_nat(0u);
v_bs_x27_3093_ = lean_array_uset(v_bs_3084_, v_i_3083_, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_fst_3087_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3094_);
v___x_3096_ = v___x_3090_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_snd_3088_);
v___x_3096_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((size_t)1ULL);
v___x_3098_ = lean_usize_add(v_i_3083_, v___x_3097_);
v___x_3099_ = lean_array_uset(v_bs_x27_3093_, v_i_3083_, v___x_3096_);
v_i_3083_ = v___x_3098_;
v_bs_3084_ = v___x_3099_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3103_, lean_object* v_i_3104_, lean_object* v_bs_3105_){
_start:
{
size_t v_sz_boxed_3106_; size_t v_i_boxed_3107_; lean_object* v_res_3108_; 
v_sz_boxed_3106_ = lean_unbox_usize(v_sz_3103_);
lean_dec(v_sz_3103_);
v_i_boxed_3107_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3106_, v_i_boxed_3107_, v_bs_3105_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3109_, lean_object* v_as_3110_, size_t v_sz_3111_, size_t v_i_3112_, lean_object* v_b_3113_){
_start:
{
lean_object* v_a_3116_; uint8_t v___x_3120_; 
v___x_3120_ = lean_usize_dec_lt(v_i_3112_, v_sz_3111_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3113_);
return v___x_3121_;
}
else
{
lean_object* v_a_3122_; lean_object* v_snd_3123_; lean_object* v_snd_3124_; lean_object* v_fst_3125_; lean_object* v_fst_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3176_; 
v_a_3122_ = lean_array_uget(v_as_3110_, v_i_3112_);
v_snd_3123_ = lean_ctor_get(v_a_3122_, 1);
lean_inc(v_snd_3123_);
v_snd_3124_ = lean_ctor_get(v_b_3113_, 1);
lean_inc(v_snd_3124_);
v_fst_3125_ = lean_ctor_get(v_a_3122_, 0);
v_fst_3126_ = lean_ctor_get(v_snd_3123_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_snd_3123_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v_snd_3123_, 1);
lean_dec(v_unused_3177_);
v___x_3128_ = v_snd_3123_;
v_isShared_3129_ = v_isSharedCheck_3176_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_fst_3126_);
lean_dec(v_snd_3123_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3176_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_fst_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3174_; 
v_fst_3130_ = lean_ctor_get(v_b_3113_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_b_3113_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_b_3113_, 1);
lean_dec(v_unused_3175_);
v___x_3132_ = v_b_3113_;
v_isShared_3133_ = v_isSharedCheck_3174_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_fst_3130_);
lean_dec(v_b_3113_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3174_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_fst_3134_; lean_object* v_snd_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3173_; 
v_fst_3134_ = lean_ctor_get(v_snd_3124_, 0);
v_snd_3135_ = lean_ctor_get(v_snd_3124_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_snd_3124_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3137_ = v_snd_3124_;
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_snd_3135_);
lean_inc(v_fst_3134_);
lean_dec(v_snd_3124_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
uint8_t v___x_3151_; 
v___x_3151_ = l_Lean_NameSet_contains(v_forbidden_3109_, v_fst_3125_);
if (v___x_3151_ == 0)
{
uint8_t v___x_3152_; 
lean_inc(v_fst_3125_);
v___x_3152_ = lean_unbox(v_fst_3126_);
lean_dec(v_fst_3126_);
if (v___x_3152_ == 0)
{
uint8_t v___x_3153_; 
lean_del_object(v___x_3137_);
lean_del_object(v___x_3132_);
v___x_3153_ = l_Lean_NameSet_contains(v_fst_3130_, v_fst_3125_);
if (v___x_3153_ == 0)
{
if (v___x_3120_ == 0)
{
lean_dec(v_fst_3125_);
lean_dec(v_a_3122_);
goto v___jp_3146_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_del_object(v___x_3128_);
v___x_3154_ = lean_array_push(v_snd_3135_, v_a_3122_);
v___x_3155_ = l_Lean_NameSet_insert(v_fst_3130_, v_fst_3125_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_fst_3134_);
lean_ctor_set(v___x_3156_, 1, v___x_3154_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v_a_3116_ = v___x_3157_;
goto v___jp_3115_;
}
}
else
{
lean_dec(v_fst_3125_);
lean_dec(v_a_3122_);
goto v___jp_3146_;
}
}
else
{
uint8_t v___x_3158_; 
lean_del_object(v___x_3128_);
v___x_3158_ = l_Lean_NameSet_contains(v_fst_3134_, v_fst_3125_);
if (v___x_3158_ == 0)
{
if (v___x_3120_ == 0)
{
lean_dec(v_fst_3125_);
lean_dec(v_a_3122_);
goto v___jp_3139_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_del_object(v___x_3137_);
lean_del_object(v___x_3132_);
v___x_3159_ = lean_array_push(v_snd_3135_, v_a_3122_);
v___x_3160_ = l_Lean_NameSet_insert(v_fst_3134_, v_fst_3125_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_fst_3130_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v_a_3116_ = v___x_3162_;
goto v___jp_3115_;
}
}
else
{
lean_dec(v_fst_3125_);
lean_dec(v_a_3122_);
goto v___jp_3139_;
}
}
}
else
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_3137_);
lean_del_object(v___x_3132_);
lean_del_object(v___x_3128_);
lean_dec(v_fst_3126_);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3122_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; 
v_unused_3171_ = lean_ctor_get(v_a_3122_, 1);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_a_3122_, 0);
lean_dec(v_unused_3172_);
v___x_3164_ = v_a_3122_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_a_3122_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 1, v_snd_3135_);
lean_ctor_set(v___x_3164_, 0, v_fst_3134_);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_fst_3134_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_snd_3135_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_fst_3130_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v_a_3116_ = v___x_3168_;
goto v___jp_3115_;
}
}
}
v___jp_3139_:
{
lean_object* v___x_3141_; 
if (v_isShared_3138_ == 0)
{
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_fst_3134_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_snd_3135_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 1, v___x_3141_);
v___x_3143_ = v___x_3132_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_fst_3130_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
v_a_3116_ = v___x_3143_;
goto v___jp_3115_;
}
}
}
v___jp_3146_:
{
lean_object* v___x_3148_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v_snd_3135_);
lean_ctor_set(v___x_3128_, 0, v_fst_3134_);
v___x_3148_ = v___x_3128_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_fst_3134_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_snd_3135_);
v___x_3148_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_fst_3130_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v_a_3116_ = v___x_3149_;
goto v___jp_3115_;
}
}
}
}
}
}
v___jp_3115_:
{
size_t v___x_3117_; size_t v___x_3118_; 
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_add(v_i_3112_, v___x_3117_);
v_i_3112_ = v___x_3118_;
v_b_3113_ = v_a_3116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3178_, lean_object* v_as_3179_, lean_object* v_sz_3180_, lean_object* v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_){
_start:
{
size_t v_sz_boxed_3184_; size_t v_i_boxed_3185_; lean_object* v_res_3186_; 
v_sz_boxed_3184_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3185_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3178_, v_as_3179_, v_sz_boxed_3184_, v_i_boxed_3185_, v_b_3182_);
lean_dec_ref(v_as_3179_);
lean_dec(v_forbidden_3178_);
return v_res_3186_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3191_ = l_Lean_MessageData_ofFormat(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_box(1);
v___x_3193_ = l_Lean_MessageData_ofFormat(v___x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
if (lean_obj_tag(v_a_3196_) == 0)
{
lean_object* v___x_3198_; 
v___x_3198_ = l_List_reverse___redArg(v_a_3197_);
return v___x_3198_;
}
else
{
lean_object* v_head_3199_; lean_object* v_snd_3200_; lean_object* v_tail_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3246_; 
v_head_3199_ = lean_ctor_get(v_a_3196_, 0);
lean_inc(v_head_3199_);
v_snd_3200_ = lean_ctor_get(v_head_3199_, 1);
lean_inc(v_snd_3200_);
v_tail_3201_ = lean_ctor_get(v_a_3196_, 1);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_a_3196_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v_a_3196_, 0);
lean_dec(v_unused_3247_);
v___x_3203_ = v_a_3196_;
v_isShared_3204_ = v_isSharedCheck_3246_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_tail_3201_);
lean_dec(v_a_3196_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3246_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_fst_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3244_; 
v_fst_3205_ = lean_ctor_get(v_head_3199_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_head_3199_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_head_3199_, 1);
lean_dec(v_unused_3245_);
v___x_3207_ = v_head_3199_;
v_isShared_3208_ = v_isSharedCheck_3244_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_fst_3205_);
lean_dec(v_head_3199_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3244_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_fst_3209_; lean_object* v_snd_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3243_; 
v_fst_3209_ = lean_ctor_get(v_snd_3200_, 0);
v_snd_3210_ = lean_ctor_get(v_snd_3200_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_snd_3200_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3212_ = v_snd_3200_;
v_isShared_3213_ = v_isSharedCheck_3243_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_snd_3210_);
lean_inc(v_fst_3209_);
lean_dec(v_snd_3200_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3243_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = l_Lean_MessageData_ofName(v_fst_3205_);
v___x_3215_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3213_ == 0)
{
lean_ctor_set_tag(v___x_3212_, 7);
lean_ctor_set(v___x_3212_, 1, v___x_3215_);
lean_ctor_set(v___x_3212_, 0, v___x_3214_);
v___x_3217_ = v___x_3212_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3208_ == 0)
{
lean_ctor_set_tag(v___x_3207_, 7);
lean_ctor_set(v___x_3207_, 1, v___x_3218_);
lean_ctor_set(v___x_3207_, 0, v___x_3217_);
v___x_3220_ = v___x_3207_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___y_3222_; uint8_t v___x_3238_; 
v___x_3238_ = lean_unbox(v_fst_3209_);
lean_dec(v_fst_3209_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3222_ = v___x_3239_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3222_ = v___x_3240_;
goto v___jp_3221_;
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3222_);
v___x_3224_ = l_Lean_MessageData_ofFormat(v___x_3223_);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3215_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v___x_3218_);
v___x_3227_ = l_Nat_reprFast(v_snd_3210_);
v___x_3228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___x_3229_ = l_Lean_MessageData_ofFormat(v___x_3228_);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3226_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_MessageData_paren(v___x_3230_);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3220_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = l_Lean_MessageData_paren(v___x_3232_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v_a_3197_);
lean_ctor_set(v___x_3203_, 0, v___x_3233_);
v___x_3235_ = v___x_3203_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_a_3197_);
v___x_3235_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
v_a_3196_ = v_tail_3201_;
v_a_3197_ = v___x_3235_;
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
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3250_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3251_ = l_Lean_NameSet_empty;
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3250_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3254_ = l_Lean_NameSet_empty;
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3253_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__4(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__3));
v___x_3258_ = l_Lean_stringToMessageData(v___x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3259_, lean_object* v_moduleRef_3260_, lean_object* v_target_3261_, lean_object* v_forbidden_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3268_, 0, v_moduleRef_3260_);
v___x_3269_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3268_, v_target_3261_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; size_t v_sz_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_array_get_size(v_a_3270_);
v___x_3273_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3270_, v___x_3271_, v___x_3272_);
v___x_3274_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3275_ = lean_array_size(v___x_3273_);
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3262_, v___x_3273_, v_sz_3275_, v___x_3276_, v___x_3274_);
lean_dec_ref(v___x_3273_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_snd_3281_; lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3319_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3280_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Rewrites_rwLemma_spec__2___redArg(v___x_3279_, v_a_3265_);
v_snd_3281_ = lean_ctor_get(v_a_3278_, 1);
lean_inc(v_snd_3281_);
lean_dec(v_a_3278_);
v_a_3282_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3284_ = v___x_3280_;
v_isShared_3285_ = v_isSharedCheck_3319_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3319_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_snd_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3317_; 
v_snd_3286_ = lean_ctor_get(v_snd_3281_, 1);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_snd_3281_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v_snd_3281_, 0);
lean_dec(v_unused_3318_);
v___x_3288_ = v_snd_3281_;
v_isShared_3289_ = v_isSharedCheck_3317_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_snd_3286_);
lean_dec(v_snd_3281_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3317_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_unbox(v_a_3282_);
lean_dec(v_a_3282_);
if (v___x_3299_ == 0)
{
lean_del_object(v___x_3288_);
goto v___jp_3290_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3300_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__4, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__4);
lean_inc(v_snd_3286_);
v___x_3301_ = lean_array_to_list(v_snd_3286_);
v___x_3302_ = lean_box(0);
v___x_3303_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3301_, v___x_3302_);
v___x_3304_ = l_Lean_MessageData_ofList(v___x_3303_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 7);
lean_ctor_set(v___x_3288_, 1, v___x_3304_);
lean_ctor_set(v___x_3288_, 0, v___x_3300_);
v___x_3306_ = v___x_3288_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__3(v___x_3279_, v___x_3306_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref(v___x_3307_);
goto v___jp_3290_;
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v_snd_3286_);
lean_del_object(v___x_3284_);
lean_dec_ref(v_hyps_3259_);
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
v___jp_3290_:
{
size_t v_sz_3291_; lean_object* v___x_3292_; size_t v_sz_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v_sz_3291_ = lean_array_size(v_hyps_3259_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3291_, v___x_3276_, v_hyps_3259_);
v_sz_3293_ = lean_array_size(v_snd_3286_);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3293_, v___x_3276_, v_snd_3286_);
v___x_3295_ = l_Array_append___redArg(v___x_3292_, v___x_3294_);
lean_dec_ref(v___x_3294_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3295_);
v___x_3297_ = v___x_3284_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v_hyps_3259_);
v_a_3320_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3277_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3277_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec_ref(v_hyps_3259_);
v_a_3328_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3269_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3269_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3336_, lean_object* v_moduleRef_3337_, lean_object* v_target_3338_, lean_object* v_forbidden_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3336_, v_moduleRef_3337_, v_target_3338_, v_forbidden_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_forbidden_3339_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3346_, lean_object* v_as_3347_, size_t v_sz_3348_, size_t v_i_3349_, lean_object* v_b_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3346_, v_as_3347_, v_sz_3348_, v_i_3349_, v_b_3350_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3357_, lean_object* v_as_3358_, lean_object* v_sz_3359_, lean_object* v_i_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
size_t v_sz_boxed_3367_; size_t v_i_boxed_3368_; lean_object* v_res_3369_; 
v_sz_boxed_3367_ = lean_unbox_usize(v_sz_3359_);
lean_dec(v_sz_3359_);
v_i_boxed_3368_ = lean_unbox_usize(v_i_3360_);
lean_dec(v_i_3360_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3357_, v_as_3358_, v_sz_boxed_3367_, v_i_boxed_3368_, v_b_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec_ref(v_as_3358_);
lean_dec(v_forbidden_3357_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3370_, lean_object* v_j_3371_, lean_object* v_h_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3370_, v_j_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3374_){
_start:
{
uint8_t v_rfl_x3f_3375_; 
v_rfl_x3f_3375_ = lean_ctor_get_uint8(v_r_3374_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3375_ == 0)
{
lean_object* v_result_3376_; lean_object* v_eNew_3377_; lean_object* v___x_3378_; 
v_result_3376_ = lean_ctor_get(v_r_3374_, 2);
v_eNew_3377_ = lean_ctor_get(v_result_3376_, 0);
lean_inc_ref(v_eNew_3377_);
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_eNew_3377_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_box(0);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3380_);
lean_dec_ref(v_r_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
lean_inc(v___y_3386_);
lean_inc_ref(v___y_3385_);
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
v___x_3392_ = lean_apply_9(v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, lean_box(0));
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3404_, lean_object* v_x_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___f_3415_; lean_object* v___x_3416_; 
lean_inc(v___y_3409_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3406_);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3415_, 0, v_x_3405_);
lean_closure_set(v___f_3415_, 1, v___y_3406_);
lean_closure_set(v___f_3415_, 2, v___y_3407_);
lean_closure_set(v___f_3415_, 3, v___y_3408_);
lean_closure_set(v___f_3415_, 4, v___y_3409_);
v___x_3416_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3404_, v___f_3415_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3416_) == 0)
{
return v___x_3416_;
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3425_, lean_object* v_x_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3425_, v_x_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3437_, lean_object* v_mctx_3438_, lean_object* v_x_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3438_, v_x_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3450_, lean_object* v_mctx_3451_, lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3450_, v_mctx_3451_, v_x_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3463_, uint8_t v_symm_3464_, lean_object* v_r_3465_, lean_object* v_ref_3466_, lean_object* v_checkState_x3f_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3469_, v___y_3471_, v___y_3473_, v___y_3475_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_ref_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___y_3489_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v_ref_3479_ = lean_ctor_get(v___y_3474_, 5);
v___x_3480_ = lean_box(v_symm_3464_);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_expr_3463_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3465_);
v___x_3485_ = l_Option_toLOption___redArg(v___x_3484_);
v___x_3486_ = lean_box(0);
lean_inc(v_ref_3479_);
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_ref_3479_);
if (lean_obj_tag(v_checkState_x3f_3467_) == 0)
{
v___y_3489_ = v_a_3478_;
goto v___jp_3488_;
}
else
{
lean_object* v_val_3492_; 
lean_dec(v_a_3478_);
v_val_3492_ = lean_ctor_get(v_checkState_x3f_3467_, 0);
lean_inc(v_val_3492_);
lean_dec_ref(v_checkState_x3f_3467_);
v___y_3489_ = v_val_3492_;
goto v___jp_3488_;
}
v___jp_3488_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___y_3489_);
v___x_3491_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3466_, v___x_3483_, v___x_3485_, v___x_3486_, v___x_3487_, v___x_3490_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
return v___x_3491_;
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_checkState_x3f_3467_);
lean_dec(v_ref_3466_);
lean_dec_ref(v_expr_3463_);
v_a_3493_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3477_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3477_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3501_, lean_object* v_symm_3502_, lean_object* v_r_3503_, lean_object* v_ref_3504_, lean_object* v_checkState_x3f_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v_symm_boxed_3515_; lean_object* v_res_3516_; 
v_symm_boxed_3515_ = lean_unbox(v_symm_3502_);
v_res_3516_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3501_, v_symm_boxed_3515_, v_r_3503_, v_ref_3504_, v_checkState_x3f_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v_r_3503_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3517_, lean_object* v_r_3518_, lean_object* v_checkState_x3f_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_expr_3529_; uint8_t v_symm_3530_; lean_object* v_mctx_3531_; lean_object* v___x_3532_; lean_object* v___f_3533_; lean_object* v___x_3534_; 
v_expr_3529_ = lean_ctor_get(v_r_3518_, 0);
lean_inc_ref(v_expr_3529_);
v_symm_3530_ = lean_ctor_get_uint8(v_r_3518_, sizeof(void*)*4);
v_mctx_3531_ = lean_ctor_get(v_r_3518_, 3);
lean_inc_ref(v_mctx_3531_);
v___x_3532_ = lean_box(v_symm_3530_);
v___f_3533_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3533_, 0, v_expr_3529_);
lean_closure_set(v___f_3533_, 1, v___x_3532_);
lean_closure_set(v___f_3533_, 2, v_r_3518_);
lean_closure_set(v___f_3533_, 3, v_ref_3517_);
lean_closure_set(v___f_3533_, 4, v_checkState_x3f_3519_);
v___x_3534_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3531_, v___f_3533_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3535_, lean_object* v_r_3536_, lean_object* v_checkState_x3f_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3535_, v_r_3536_, v_checkState_x3f_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3548_, lean_object* v_b_3549_, lean_object* v_x_3550_){
_start:
{
if (lean_obj_tag(v_x_3550_) == 0)
{
lean_dec(v_b_3549_);
lean_dec_ref(v_a_3548_);
return v_x_3550_;
}
else
{
lean_object* v_key_3551_; lean_object* v_value_3552_; lean_object* v_tail_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3565_; 
v_key_3551_ = lean_ctor_get(v_x_3550_, 0);
v_value_3552_ = lean_ctor_get(v_x_3550_, 1);
v_tail_3553_ = lean_ctor_get(v_x_3550_, 2);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_x_3550_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3555_ = v_x_3550_;
v_isShared_3556_ = v_isSharedCheck_3565_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_tail_3553_);
lean_inc(v_value_3552_);
lean_inc(v_key_3551_);
lean_dec(v_x_3550_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3565_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
uint8_t v___x_3557_; 
v___x_3557_ = lean_string_dec_eq(v_key_3551_, v_a_3548_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3548_, v_b_3549_, v_tail_3553_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 2, v___x_3558_);
v___x_3560_ = v___x_3555_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_key_3551_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_value_3552_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
else
{
lean_object* v___x_3563_; 
lean_dec(v_value_3552_);
lean_dec(v_key_3551_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v_b_3549_);
lean_ctor_set(v___x_3555_, 0, v_a_3548_);
v___x_3563_ = v___x_3555_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_b_3549_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_tail_3553_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 0)
{
return v_x_3566_;
}
else
{
lean_object* v_key_3568_; lean_object* v_value_3569_; lean_object* v_tail_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3593_; 
v_key_3568_ = lean_ctor_get(v_x_3567_, 0);
v_value_3569_ = lean_ctor_get(v_x_3567_, 1);
v_tail_3570_ = lean_ctor_get(v_x_3567_, 2);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_x_3567_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3572_ = v_x_3567_;
v_isShared_3573_ = v_isSharedCheck_3593_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_tail_3570_);
lean_inc(v_value_3569_);
lean_inc(v_key_3568_);
lean_dec(v_x_3567_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3593_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; uint64_t v___x_3575_; uint64_t v___x_3576_; uint64_t v___x_3577_; uint64_t v_fold_3578_; uint64_t v___x_3579_; uint64_t v___x_3580_; uint64_t v___x_3581_; size_t v___x_3582_; size_t v___x_3583_; size_t v___x_3584_; size_t v___x_3585_; size_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3574_ = lean_array_get_size(v_x_3566_);
v___x_3575_ = lean_string_hash(v_key_3568_);
v___x_3576_ = 32ULL;
v___x_3577_ = lean_uint64_shift_right(v___x_3575_, v___x_3576_);
v_fold_3578_ = lean_uint64_xor(v___x_3575_, v___x_3577_);
v___x_3579_ = 16ULL;
v___x_3580_ = lean_uint64_shift_right(v_fold_3578_, v___x_3579_);
v___x_3581_ = lean_uint64_xor(v_fold_3578_, v___x_3580_);
v___x_3582_ = lean_uint64_to_usize(v___x_3581_);
v___x_3583_ = lean_usize_of_nat(v___x_3574_);
v___x_3584_ = ((size_t)1ULL);
v___x_3585_ = lean_usize_sub(v___x_3583_, v___x_3584_);
v___x_3586_ = lean_usize_land(v___x_3582_, v___x_3585_);
v___x_3587_ = lean_array_uget_borrowed(v_x_3566_, v___x_3586_);
lean_inc(v___x_3587_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 2, v___x_3587_);
v___x_3589_ = v___x_3572_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_key_3568_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_value_3569_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_array_uset(v_x_3566_, v___x_3586_, v___x_3589_);
v_x_3566_ = v___x_3590_;
v_x_3567_ = v_tail_3570_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3594_, lean_object* v_source_3595_, lean_object* v_target_3596_){
_start:
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = lean_array_get_size(v_source_3595_);
v___x_3598_ = lean_nat_dec_lt(v_i_3594_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_dec_ref(v_source_3595_);
lean_dec(v_i_3594_);
return v_target_3596_;
}
else
{
lean_object* v_es_3599_; lean_object* v___x_3600_; lean_object* v_source_3601_; lean_object* v_target_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_es_3599_ = lean_array_fget(v_source_3595_, v_i_3594_);
v___x_3600_ = lean_box(0);
v_source_3601_ = lean_array_fset(v_source_3595_, v_i_3594_, v___x_3600_);
v_target_3602_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3596_, v_es_3599_);
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = lean_nat_add(v_i_3594_, v___x_3603_);
lean_dec(v_i_3594_);
v_i_3594_ = v___x_3604_;
v_source_3595_ = v_source_3601_;
v_target_3596_ = v_target_3602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3606_){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v_nbuckets_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3607_ = lean_array_get_size(v_data_3606_);
v___x_3608_ = lean_unsigned_to_nat(2u);
v_nbuckets_3609_ = lean_nat_mul(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_box(0);
v___x_3612_ = lean_mk_array(v_nbuckets_3609_, v___x_3611_);
v___x_3613_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3610_, v_data_3606_, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3614_, lean_object* v_x_3615_){
_start:
{
if (lean_obj_tag(v_x_3615_) == 0)
{
uint8_t v___x_3616_; 
v___x_3616_ = 0;
return v___x_3616_;
}
else
{
lean_object* v_key_3617_; lean_object* v_tail_3618_; uint8_t v___x_3619_; 
v_key_3617_ = lean_ctor_get(v_x_3615_, 0);
v_tail_3618_ = lean_ctor_get(v_x_3615_, 2);
v___x_3619_ = lean_string_dec_eq(v_key_3617_, v_a_3614_);
if (v___x_3619_ == 0)
{
v_x_3615_ = v_tail_3618_;
goto _start;
}
else
{
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3621_, lean_object* v_x_3622_){
_start:
{
uint8_t v_res_3623_; lean_object* v_r_3624_; 
v_res_3623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3621_, v_x_3622_);
lean_dec(v_x_3622_);
lean_dec_ref(v_a_3621_);
v_r_3624_ = lean_box(v_res_3623_);
return v_r_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3625_, lean_object* v_a_3626_, lean_object* v_b_3627_){
_start:
{
lean_object* v_size_3628_; lean_object* v_buckets_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3672_; 
v_size_3628_ = lean_ctor_get(v_m_3625_, 0);
v_buckets_3629_ = lean_ctor_get(v_m_3625_, 1);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_m_3625_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3631_ = v_m_3625_;
v_isShared_3632_ = v_isSharedCheck_3672_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_buckets_3629_);
lean_inc(v_size_3628_);
lean_dec(v_m_3625_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3672_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; uint64_t v___x_3636_; uint64_t v_fold_3637_; uint64_t v___x_3638_; uint64_t v___x_3639_; uint64_t v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; size_t v___x_3645_; lean_object* v_bkt_3646_; uint8_t v___x_3647_; 
v___x_3633_ = lean_array_get_size(v_buckets_3629_);
v___x_3634_ = lean_string_hash(v_a_3626_);
v___x_3635_ = 32ULL;
v___x_3636_ = lean_uint64_shift_right(v___x_3634_, v___x_3635_);
v_fold_3637_ = lean_uint64_xor(v___x_3634_, v___x_3636_);
v___x_3638_ = 16ULL;
v___x_3639_ = lean_uint64_shift_right(v_fold_3637_, v___x_3638_);
v___x_3640_ = lean_uint64_xor(v_fold_3637_, v___x_3639_);
v___x_3641_ = lean_uint64_to_usize(v___x_3640_);
v___x_3642_ = lean_usize_of_nat(v___x_3633_);
v___x_3643_ = ((size_t)1ULL);
v___x_3644_ = lean_usize_sub(v___x_3642_, v___x_3643_);
v___x_3645_ = lean_usize_land(v___x_3641_, v___x_3644_);
v_bkt_3646_ = lean_array_uget_borrowed(v_buckets_3629_, v___x_3645_);
v___x_3647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3626_, v_bkt_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v_size_x27_3649_; lean_object* v___x_3650_; lean_object* v_buckets_x27_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v_size_x27_3649_ = lean_nat_add(v_size_3628_, v___x_3648_);
lean_dec(v_size_3628_);
lean_inc(v_bkt_3646_);
v___x_3650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3650_, 0, v_a_3626_);
lean_ctor_set(v___x_3650_, 1, v_b_3627_);
lean_ctor_set(v___x_3650_, 2, v_bkt_3646_);
v_buckets_x27_3651_ = lean_array_uset(v_buckets_3629_, v___x_3645_, v___x_3650_);
v___x_3652_ = lean_unsigned_to_nat(4u);
v___x_3653_ = lean_nat_mul(v_size_x27_3649_, v___x_3652_);
v___x_3654_ = lean_unsigned_to_nat(3u);
v___x_3655_ = lean_nat_div(v___x_3653_, v___x_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_array_get_size(v_buckets_x27_3651_);
v___x_3657_ = lean_nat_dec_le(v___x_3655_, v___x_3656_);
lean_dec(v___x_3655_);
if (v___x_3657_ == 0)
{
lean_object* v_val_3658_; lean_object* v___x_3660_; 
v_val_3658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3651_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v_val_3658_);
lean_ctor_set(v___x_3631_, 0, v_size_x27_3649_);
v___x_3660_ = v___x_3631_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_size_x27_3649_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_val_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
else
{
lean_object* v___x_3663_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v_buckets_x27_3651_);
lean_ctor_set(v___x_3631_, 0, v_size_x27_3649_);
v___x_3663_ = v___x_3631_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_size_x27_3649_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_buckets_x27_3651_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v_buckets_x27_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_inc(v_bkt_3646_);
v___x_3665_ = lean_box(0);
v_buckets_x27_3666_ = lean_array_uset(v_buckets_3629_, v___x_3645_, v___x_3665_);
v___x_3667_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3626_, v_b_3627_, v_bkt_3646_);
v___x_3668_ = lean_array_uset(v_buckets_x27_3666_, v___x_3645_, v___x_3667_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3668_);
v___x_3670_ = v___x_3631_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_size_3628_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_buckets_3675_; lean_object* v___x_3676_; uint64_t v___x_3677_; uint64_t v___x_3678_; uint64_t v___x_3679_; uint64_t v_fold_3680_; uint64_t v___x_3681_; uint64_t v___x_3682_; uint64_t v___x_3683_; size_t v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_buckets_3675_ = lean_ctor_get(v_m_3673_, 1);
v___x_3676_ = lean_array_get_size(v_buckets_3675_);
v___x_3677_ = lean_string_hash(v_a_3674_);
v___x_3678_ = 32ULL;
v___x_3679_ = lean_uint64_shift_right(v___x_3677_, v___x_3678_);
v_fold_3680_ = lean_uint64_xor(v___x_3677_, v___x_3679_);
v___x_3681_ = 16ULL;
v___x_3682_ = lean_uint64_shift_right(v_fold_3680_, v___x_3681_);
v___x_3683_ = lean_uint64_xor(v_fold_3680_, v___x_3682_);
v___x_3684_ = lean_uint64_to_usize(v___x_3683_);
v___x_3685_ = lean_usize_of_nat(v___x_3676_);
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_sub(v___x_3685_, v___x_3686_);
v___x_3688_ = lean_usize_land(v___x_3684_, v___x_3687_);
v___x_3689_ = lean_array_uget_borrowed(v_buckets_3675_, v___x_3688_);
v___x_3690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3674_, v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3691_, lean_object* v_a_3692_){
_start:
{
uint8_t v_res_3693_; lean_object* v_r_3694_; 
v_res_3693_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3691_, v_a_3692_);
lean_dec_ref(v_a_3692_);
lean_dec_ref(v_m_3691_);
v_r_3694_ = lean_box(v_res_3693_);
return v_r_3694_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3695_, lean_object* v_as_x27_3696_, lean_object* v_b_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
if (lean_obj_tag(v_as_x27_3696_) == 0)
{
lean_object* v___x_3703_; 
lean_dec_ref(v_cfg_3695_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_b_3697_);
return v___x_3703_;
}
else
{
lean_object* v_head_3704_; lean_object* v_snd_3705_; lean_object* v_tail_3706_; lean_object* v_fst_3707_; lean_object* v_fst_3708_; lean_object* v_snd_3709_; lean_object* v___x_3710_; 
v_head_3704_ = lean_ctor_get(v_as_x27_3696_, 0);
lean_inc(v_head_3704_);
v_snd_3705_ = lean_ctor_get(v_head_3704_, 1);
lean_inc(v_snd_3705_);
v_tail_3706_ = lean_ctor_get(v_as_x27_3696_, 1);
lean_inc(v_tail_3706_);
lean_dec_ref(v_as_x27_3696_);
v_fst_3707_ = lean_ctor_get(v_head_3704_, 0);
lean_inc(v_fst_3707_);
lean_dec(v_head_3704_);
v_fst_3708_ = lean_ctor_get(v_snd_3705_, 0);
lean_inc(v_fst_3708_);
v_snd_3709_ = lean_ctor_get(v_snd_3705_, 1);
lean_inc(v_snd_3709_);
lean_dec(v_snd_3705_);
v___x_3710_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3700_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_snd_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3855_; 
v_snd_3711_ = lean_ctor_get(v_b_3697_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_b_3697_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v_b_3697_, 0);
lean_dec(v_unused_3856_);
v___x_3713_ = v_b_3697_;
v_isShared_3714_ = v_isSharedCheck_3855_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_snd_3711_);
lean_dec(v_b_3697_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3855_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3854_; 
v_a_3715_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3717_ = v___x_3710_;
v_isShared_3718_ = v_isSharedCheck_3854_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3710_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3854_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_fst_3719_; lean_object* v_snd_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3853_; 
v_fst_3719_ = lean_ctor_get(v_snd_3711_, 0);
v_snd_3720_ = lean_ctor_get(v_snd_3711_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_snd_3711_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3722_ = v_snd_3711_;
v_isShared_3723_ = v_isSharedCheck_3853_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_snd_3720_);
lean_inc(v_fst_3719_);
lean_dec(v_snd_3711_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3853_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
uint8_t v_stopAtRfl_3724_; lean_object* v_max_3725_; lean_object* v_minHeartbeats_3726_; lean_object* v_goal_3727_; lean_object* v_target_3728_; uint8_t v_side_3729_; lean_object* v_mctx_3730_; uint8_t v___x_3731_; 
v_stopAtRfl_3724_ = lean_ctor_get_uint8(v_cfg_3695_, sizeof(void*)*5);
v_max_3725_ = lean_ctor_get(v_cfg_3695_, 0);
v_minHeartbeats_3726_ = lean_ctor_get(v_cfg_3695_, 1);
v_goal_3727_ = lean_ctor_get(v_cfg_3695_, 2);
v_target_3728_ = lean_ctor_get(v_cfg_3695_, 3);
v_side_3729_ = lean_ctor_get_uint8(v_cfg_3695_, sizeof(void*)*5 + 1);
v_mctx_3730_ = lean_ctor_get(v_cfg_3695_, 4);
v___x_3731_ = lean_nat_dec_lt(v_a_3715_, v_minHeartbeats_3726_);
lean_dec(v_a_3715_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = lean_array_get_size(v_snd_3720_);
v___x_3733_ = lean_nat_dec_le(v_max_3725_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_del_object(v___x_3717_);
v___x_3734_ = lean_box(v_side_3729_);
lean_inc_ref(v_target_3728_);
lean_inc(v_goal_3727_);
lean_inc_ref(v_mctx_3730_);
v___x_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3735_, 0, v_mctx_3730_);
lean_closure_set(v___x_3735_, 1, v_goal_3727_);
lean_closure_set(v___x_3735_, 2, v_target_3728_);
lean_closure_set(v___x_3735_, 3, v___x_3734_);
lean_closure_set(v___x_3735_, 4, v_fst_3707_);
lean_closure_set(v___x_3735_, 5, v_fst_3708_);
lean_closure_set(v___x_3735_, 6, v_snd_3709_);
lean_inc_ref(v_mctx_3730_);
v___x_3736_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3736_, 0, lean_box(0));
lean_closure_set(v___x_3736_, 1, v_mctx_3730_);
lean_closure_set(v___x_3736_, 2, v___x_3735_);
v___x_3737_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3736_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = lean_box(0);
if (lean_obj_tag(v_a_3738_) == 0)
{
lean_object* v___x_3741_; 
if (v_isShared_3723_ == 0)
{
v___x_3741_ = v___x_3722_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_fst_3719_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_snd_3720_);
v___x_3741_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3743_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3741_);
lean_ctor_set(v___x_3713_, 0, v___x_3739_);
v___x_3743_ = v___x_3713_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
v_as_x27_3696_ = v_tail_3706_;
v_b_3697_ = v___x_3743_;
goto _start;
}
}
}
else
{
lean_object* v_val_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3824_; 
v_val_3747_ = lean_ctor_get(v_a_3738_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3738_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3749_ = v_a_3738_;
v_isShared_3750_ = v_isSharedCheck_3824_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_val_3747_);
lean_dec(v_a_3738_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3824_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_result_3751_; lean_object* v_mctx_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_result_3751_ = lean_ctor_get(v_val_3747_, 2);
v_mctx_3752_ = lean_ctor_get(v_val_3747_, 3);
lean_inc(v_val_3747_);
v___x_3753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3753_, 0, v_val_3747_);
lean_inc_ref(v_mctx_3752_);
v___x_3754_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3754_, 0, lean_box(0));
lean_closure_set(v___x_3754_, 1, v_mctx_3752_);
lean_closure_set(v___x_3754_, 2, v___x_3753_);
v___x_3755_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3754_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; uint8_t v___x_3757_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3719_, v_a_3756_);
if (v___x_3757_ == 0)
{
lean_object* v_eNew_3758_; lean_object* v___x_3759_; 
v_eNew_3758_ = lean_ctor_get(v_result_3751_, 0);
lean_inc_ref(v_eNew_3758_);
lean_inc_ref(v_mctx_3752_);
v___x_3759_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3752_, v_eNew_3758_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
if (lean_obj_tag(v___x_3759_) == 0)
{
if (v_stopAtRfl_3724_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
lean_dec_ref(v___x_3759_);
lean_del_object(v___x_3749_);
v___x_3760_ = lean_box(0);
v___x_3761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3719_, v_a_3756_, v___x_3760_);
v___x_3762_ = lean_array_push(v_snd_3720_, v_val_3747_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v___x_3762_);
lean_ctor_set(v___x_3722_, 0, v___x_3761_);
v___x_3764_ = v___x_3722_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3766_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3764_);
lean_ctor_set(v___x_3713_, 0, v___x_3739_);
v___x_3766_ = v___x_3713_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
v_as_x27_3696_ = v_tail_3706_;
v_b_3697_ = v___x_3766_;
goto _start;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3800_; 
v_a_3770_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3772_ = v___x_3759_;
v_isShared_3773_ = v_isSharedCheck_3800_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3759_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3800_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
uint8_t v___x_3774_; 
v___x_3774_ = lean_unbox(v_a_3770_);
lean_dec(v_a_3770_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_del_object(v___x_3772_);
lean_del_object(v___x_3749_);
v___x_3775_ = lean_box(0);
v___x_3776_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3719_, v_a_3756_, v___x_3775_);
v___x_3777_ = lean_array_push(v_snd_3720_, v_val_3747_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v___x_3777_);
lean_ctor_set(v___x_3722_, 0, v___x_3776_);
v___x_3779_ = v___x_3722_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3781_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3779_);
lean_ctor_set(v___x_3713_, 0, v___x_3739_);
v___x_3781_ = v___x_3713_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
v_as_x27_3696_ = v_tail_3706_;
v_b_3697_ = v___x_3781_;
goto _start;
}
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_dec(v_a_3756_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_mk_empty_array_with_capacity(v___x_3785_);
v___x_3787_ = lean_array_push(v___x_3786_, v_val_3747_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3787_);
v___x_3789_ = v___x_3749_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3723_ == 0)
{
v___x_3791_ = v___x_3722_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fst_3719_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_snd_3720_);
v___x_3791_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3791_);
lean_ctor_set(v___x_3713_, 0, v___x_3789_);
v___x_3793_ = v___x_3713_;
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
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3793_);
v___x_3795_ = v___x_3772_;
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
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_a_3756_);
lean_del_object(v___x_3749_);
lean_dec(v_val_3747_);
lean_del_object(v___x_3722_);
lean_dec(v_snd_3720_);
lean_dec(v_fst_3719_);
lean_del_object(v___x_3713_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
v_a_3801_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3759_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3759_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v___x_3810_; 
lean_dec(v_a_3756_);
lean_del_object(v___x_3749_);
lean_dec(v_val_3747_);
if (v_isShared_3723_ == 0)
{
v___x_3810_ = v___x_3722_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_fst_3719_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_snd_3720_);
v___x_3810_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3812_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3810_);
lean_ctor_set(v___x_3713_, 0, v___x_3739_);
v___x_3812_ = v___x_3713_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
v_as_x27_3696_ = v_tail_3706_;
v_b_3697_ = v___x_3812_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_del_object(v___x_3749_);
lean_dec(v_val_3747_);
lean_del_object(v___x_3722_);
lean_dec(v_snd_3720_);
lean_dec(v_fst_3719_);
lean_del_object(v___x_3713_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
v_a_3816_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3755_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3755_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3722_);
lean_dec(v_snd_3720_);
lean_dec(v_fst_3719_);
lean_del_object(v___x_3713_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
v_a_3825_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3737_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3737_);
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
else
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_dec(v_snd_3709_);
lean_dec(v_fst_3708_);
lean_dec(v_fst_3707_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
lean_inc(v_snd_3720_);
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_snd_3720_);
if (v_isShared_3723_ == 0)
{
v___x_3835_ = v___x_3722_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_fst_3719_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_snd_3720_);
v___x_3835_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3837_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3835_);
lean_ctor_set(v___x_3713_, 0, v___x_3833_);
v___x_3837_ = v___x_3713_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3839_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3837_);
v___x_3839_ = v___x_3717_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec(v_snd_3709_);
lean_dec(v_fst_3708_);
lean_dec(v_fst_3707_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_cfg_3695_);
lean_inc(v_snd_3720_);
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_snd_3720_);
if (v_isShared_3723_ == 0)
{
v___x_3845_ = v___x_3722_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_fst_3719_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_snd_3720_);
v___x_3845_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3847_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3845_);
lean_ctor_set(v___x_3713_, 0, v___x_3843_);
v___x_3847_ = v___x_3713_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3847_);
v___x_3849_ = v___x_3717_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
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
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v_snd_3709_);
lean_dec(v_fst_3708_);
lean_dec(v_fst_3707_);
lean_dec(v_tail_3706_);
lean_dec_ref(v_b_3697_);
lean_dec_ref(v_cfg_3695_);
v_a_3857_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3710_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3710_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3865_, lean_object* v_as_x27_3866_, lean_object* v_b_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3865_, v_as_x27_3866_, v_b_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3874_, lean_object* v_seen_3875_, lean_object* v_acc_3876_, lean_object* v_xs_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v_seen_3875_);
lean_ctor_set(v___x_3884_, 1, v_acc_3876_);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3874_, v_xs_3877_, v___x_3885_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3901_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3901_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3901_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v_fst_3891_; 
v_fst_3891_ = lean_ctor_get(v_a_3887_, 0);
if (lean_obj_tag(v_fst_3891_) == 0)
{
lean_object* v_snd_3892_; lean_object* v_snd_3893_; lean_object* v___x_3895_; 
v_snd_3892_ = lean_ctor_get(v_a_3887_, 1);
lean_inc(v_snd_3892_);
lean_dec(v_a_3887_);
v_snd_3893_ = lean_ctor_get(v_snd_3892_, 1);
lean_inc(v_snd_3893_);
lean_dec(v_snd_3892_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v_snd_3893_);
v___x_3895_ = v___x_3889_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_snd_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
else
{
lean_object* v_val_3897_; lean_object* v___x_3899_; 
lean_inc_ref(v_fst_3891_);
lean_dec(v_a_3887_);
v_val_3897_ = lean_ctor_get(v_fst_3891_, 0);
lean_inc(v_val_3897_);
lean_dec_ref(v_fst_3891_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v_val_3897_);
v___x_3899_ = v___x_3889_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_val_3897_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
v_a_3902_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3886_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3886_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3910_, lean_object* v_seen_3911_, lean_object* v_acc_3912_, lean_object* v_xs_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3910_, v_seen_3911_, v_acc_3912_, v_xs_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3920_, lean_object* v_m_3921_, lean_object* v_a_3922_){
_start:
{
uint8_t v___x_3923_; 
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3921_, v_a_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3924_, lean_object* v_m_3925_, lean_object* v_a_3926_){
_start:
{
uint8_t v_res_3927_; lean_object* v_r_3928_; 
v_res_3927_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3924_, v_m_3925_, v_a_3926_);
lean_dec_ref(v_a_3926_);
lean_dec_ref(v_m_3925_);
v_r_3928_ = lean_box(v_res_3927_);
return v_r_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3929_, lean_object* v_m_3930_, lean_object* v_a_3931_, lean_object* v_b_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3930_, v_a_3931_, v_b_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3934_, lean_object* v_as_3935_, lean_object* v_as_x27_3936_, lean_object* v_b_3937_, lean_object* v_a_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3934_, v_as_x27_3936_, v_b_3937_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3945_, lean_object* v_as_3946_, lean_object* v_as_x27_3947_, lean_object* v_b_3948_, lean_object* v_a_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3945_, v_as_3946_, v_as_x27_3947_, v_b_3948_, v_a_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v_as_3946_);
return v_res_3955_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3956_, lean_object* v_a_3957_, lean_object* v_x_3958_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3957_, v_x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3960_, lean_object* v_a_3961_, lean_object* v_x_3962_){
_start:
{
uint8_t v_res_3963_; lean_object* v_r_3964_; 
v_res_3963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3960_, v_a_3961_, v_x_3962_);
lean_dec(v_x_3962_);
lean_dec_ref(v_a_3961_);
v_r_3964_ = lean_box(v_res_3963_);
return v_r_3964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3965_, lean_object* v_data_3966_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3968_, lean_object* v_a_3969_, lean_object* v_b_3970_, lean_object* v_x_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3969_, v_b_3970_, v_x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3973_, lean_object* v_i_3974_, lean_object* v_source_3975_, lean_object* v_target_3976_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3974_, v_source_3975_, v_target_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3978_, lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3979_, v_x_3980_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = lean_box(0);
v___x_3983_ = lean_unsigned_to_nat(16u);
v___x_3984_ = lean_mk_array(v___x_3983_, v___x_3982_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v___x_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3988_, lean_object* v_moduleRef_3989_, lean_object* v_goal_3990_, lean_object* v_target_3991_, lean_object* v_forbidden_3992_, uint8_t v_side_3993_, uint8_t v_stopAtRfl_3994_, lean_object* v_max_3995_, lean_object* v_leavePercentHeartbeats_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_st_ref_get(v_a_3998_);
lean_inc_ref(v_target_3991_);
v___x_4003_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3988_, v_moduleRef_3989_, v_target_3991_, v_forbidden_3992_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v___x_4003_);
v___x_4005_ = l_Lean_getMaxHeartbeats___redArg(v_a_3999_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v_mctx_4007_; lean_object* v_minHeartbeats_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
v_mctx_4007_ = lean_ctor_get(v___x_4002_, 0);
lean_inc_ref(v_mctx_4007_);
lean_dec(v___x_4002_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = lean_nat_dec_eq(v_a_4006_, v___x_4036_);
lean_dec(v_a_4006_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3999_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref(v___x_4038_);
v___x_4040_ = lean_nat_mul(v_leavePercentHeartbeats_3996_, v_a_4039_);
lean_dec(v_a_4039_);
v___x_4041_ = lean_unsigned_to_nat(100u);
v___x_4042_ = lean_nat_div(v___x_4040_, v___x_4041_);
lean_dec(v___x_4040_);
v_minHeartbeats_4009_ = v___x_4042_;
v___y_4010_ = v_a_3997_;
v___y_4011_ = v_a_3998_;
v___y_4012_ = v_a_3999_;
v___y_4013_ = v_a_4000_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec_ref(v_mctx_4007_);
lean_dec(v_a_4004_);
lean_dec(v_max_3995_);
lean_dec_ref(v_target_3991_);
lean_dec(v_goal_3990_);
v_a_4043_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4038_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4038_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
v_minHeartbeats_4009_ = v___x_4036_;
v___y_4010_ = v_a_3997_;
v___y_4011_ = v_a_3998_;
v___y_4012_ = v_a_3999_;
v___y_4013_ = v_a_4000_;
goto v___jp_4008_;
}
v___jp_4008_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_inc(v_max_3995_);
v___x_4014_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4014_, 0, v_max_3995_);
lean_ctor_set(v___x_4014_, 1, v_minHeartbeats_4009_);
lean_ctor_set(v___x_4014_, 2, v_goal_3990_);
lean_ctor_set(v___x_4014_, 3, v_target_3991_);
lean_ctor_set(v___x_4014_, 4, v_mctx_4007_);
lean_ctor_set_uint8(v___x_4014_, sizeof(void*)*5, v_stopAtRfl_3994_);
lean_ctor_set_uint8(v___x_4014_, sizeof(void*)*5 + 1, v_side_3993_);
v___x_4015_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_4016_ = lean_mk_empty_array_with_capacity(v_max_3995_);
lean_dec(v_max_3995_);
v___x_4017_ = lean_array_to_list(v_a_4004_);
v___x_4018_ = l_Lean_Meta_Rewrites_takeListAux(v___x_4014_, v___x_4015_, v___x_4016_, v___x_4017_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4027_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4023_ = lean_array_to_list(v_a_4019_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4023_);
v___x_4025_ = v___x_4021_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4018_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4018_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_4004_);
lean_dec(v___x_4002_);
lean_dec(v_max_3995_);
lean_dec_ref(v_target_3991_);
lean_dec(v_goal_3990_);
v_a_4051_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4005_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4005_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v___x_4002_);
lean_dec(v_max_3995_);
lean_dec_ref(v_target_3991_);
lean_dec(v_goal_3990_);
v_a_4059_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4003_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4003_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4067_, lean_object* v_moduleRef_4068_, lean_object* v_goal_4069_, lean_object* v_target_4070_, lean_object* v_forbidden_4071_, lean_object* v_side_4072_, lean_object* v_stopAtRfl_4073_, lean_object* v_max_4074_, lean_object* v_leavePercentHeartbeats_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
uint8_t v_side_boxed_4081_; uint8_t v_stopAtRfl_boxed_4082_; lean_object* v_res_4083_; 
v_side_boxed_4081_ = lean_unbox(v_side_4072_);
v_stopAtRfl_boxed_4082_ = lean_unbox(v_stopAtRfl_4073_);
v_res_4083_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4067_, v_moduleRef_4068_, v_goal_4069_, v_target_4070_, v_forbidden_4071_, v_side_boxed_4081_, v_stopAtRfl_boxed_4082_, v_max_4074_, v_leavePercentHeartbeats_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_leavePercentHeartbeats_4075_);
lean_dec(v_forbidden_4071_);
return v_res_4083_;
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
res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState);
res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
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

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
lean_dec_ref(v_fst_825_);
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
lean_dec_ref(v_fst_854_);
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
lean_dec_ref(v_a_891_);
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
lean_dec_ref(v_a_1031_);
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
lean_dec_ref(v_a_1031_);
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
lean_dec_ref(v_fst_1049_);
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
lean_dec_ref(v___x_1109_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2____boxed(lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState(void){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object* v___x_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_st_mk_ref(v___x_1221_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object* v___x_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(v___x_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = lean_box(0);
v___f_1232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_));
v___x_1233_ = lean_box(2);
v___x_1234_ = l_Lean_registerEnvExtension___redArg(v___f_1232_, v___x_1231_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
return v_res_1236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_unsigned_to_nat(6500u);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
lean_object* v_snd_1240_; uint8_t v___x_1241_; 
v_snd_1240_ = lean_ctor_get(v_x_1239_, 1);
v___x_1241_ = lean_unbox(v_snd_1240_);
if (v___x_1241_ == 0)
{
lean_object* v_fst_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
v_fst_1242_ = lean_ctor_get(v_x_1239_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_x_1239_, 1);
lean_dec(v_unused_1255_);
v___x_1244_ = v_x_1239_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_fst_1242_);
lean_dec(v_x_1239_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1246_ = 0;
v___x_1247_ = lean_unsigned_to_nat(2u);
v___x_1248_ = lean_nat_mul(v___x_1247_, v_x_1238_);
lean_dec(v_x_1238_);
v___x_1249_ = lean_box(v___x_1246_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1248_);
lean_ctor_set(v___x_1244_, 0, v___x_1249_);
v___x_1251_ = v___x_1244_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1248_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_fst_1242_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
}
else
{
lean_object* v_fst_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1266_; 
v_fst_1256_ = lean_ctor_get(v_x_1239_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_x_1239_, 1);
lean_dec(v_unused_1267_);
v___x_1258_ = v_x_1239_;
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_fst_1256_);
lean_dec(v_x_1239_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1260_ = 1;
v___x_1261_ = lean_box(v___x_1260_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v_x_1238_);
lean_ctor_set(v___x_1258_, 0, v___x_1261_);
v___x_1263_ = v___x_1258_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_x_1238_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_fst_1256_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1269_, lean_object* v_ty_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1276_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1279_ = lean_unsigned_to_nat(6500u);
v___x_1280_ = lean_box(0);
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1282_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1269_, v___x_1276_, v___x_1277_, v___x_1278_, v___x_1279_, v___x_1280_, v___x_1281_, v_ty_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1283_, lean_object* v_ty_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1283_, v_ty_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1298_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1298_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1315_, v_x_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1323_, lean_object* v_mctx_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_mctx_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1332_, v_mctx_1333_, v_x_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_saveState___redArg(v___y_1343_, v___y_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_r_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
v_r_1349_ = lean_apply_5(v_x_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, lean_box(0));
if (lean_obj_tag(v_r_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v_r_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v_r_1349_);
v___x_1351_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1348_, v___y_1343_, v___y_1345_);
lean_dec(v_a_1348_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1351_, 0);
lean_dec(v_unused_1359_);
v___x_1353_ = v___x_1351_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v___x_1351_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_a_1350_);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1350_);
v_a_1360_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1351_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1351_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v_r_1349_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v_r_1349_);
v___x_1369_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1348_, v___y_1343_, v___y_1345_);
lean_dec(v_a_1348_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1377_);
v___x_1371_ = v___x_1369_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v___x_1369_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 1);
lean_ctor_set(v___x_1371_, 0, v_a_1368_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1368_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_a_1368_);
v_a_1378_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1369_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1369_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_x_1341_);
v_a_1386_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1347_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1347_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1417_; uint64_t v___x_1418_; 
v___x_1417_ = 2;
v___x_1418_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1419_, uint8_t v___x_1420_, lean_object* v___x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Meta_mkFreshExprMVar(v___x_1419_, v___x_1420_, v___x_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; uint8_t v_foApprox_1430_; uint8_t v_ctxApprox_1431_; uint8_t v_quasiPatternApprox_1432_; uint8_t v_constApprox_1433_; uint8_t v_isDefEqStuckEx_1434_; uint8_t v_unificationHints_1435_; uint8_t v_proofIrrelevance_1436_; uint8_t v_assignSyntheticOpaque_1437_; uint8_t v_offsetCnstrs_1438_; uint8_t v_etaStruct_1439_; uint8_t v_univApprox_1440_; uint8_t v_iota_1441_; uint8_t v_beta_1442_; uint8_t v_proj_1443_; uint8_t v_zeta_1444_; uint8_t v_zetaDelta_1445_; uint8_t v_zetaUnused_1446_; uint8_t v_zetaHave_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1506_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Meta_Context_config(v___y_1422_);
v_foApprox_1430_ = lean_ctor_get_uint8(v___x_1429_, 0);
v_ctxApprox_1431_ = lean_ctor_get_uint8(v___x_1429_, 1);
v_quasiPatternApprox_1432_ = lean_ctor_get_uint8(v___x_1429_, 2);
v_constApprox_1433_ = lean_ctor_get_uint8(v___x_1429_, 3);
v_isDefEqStuckEx_1434_ = lean_ctor_get_uint8(v___x_1429_, 4);
v_unificationHints_1435_ = lean_ctor_get_uint8(v___x_1429_, 5);
v_proofIrrelevance_1436_ = lean_ctor_get_uint8(v___x_1429_, 6);
v_assignSyntheticOpaque_1437_ = lean_ctor_get_uint8(v___x_1429_, 7);
v_offsetCnstrs_1438_ = lean_ctor_get_uint8(v___x_1429_, 8);
v_etaStruct_1439_ = lean_ctor_get_uint8(v___x_1429_, 10);
v_univApprox_1440_ = lean_ctor_get_uint8(v___x_1429_, 11);
v_iota_1441_ = lean_ctor_get_uint8(v___x_1429_, 12);
v_beta_1442_ = lean_ctor_get_uint8(v___x_1429_, 13);
v_proj_1443_ = lean_ctor_get_uint8(v___x_1429_, 14);
v_zeta_1444_ = lean_ctor_get_uint8(v___x_1429_, 15);
v_zetaDelta_1445_ = lean_ctor_get_uint8(v___x_1429_, 16);
v_zetaUnused_1446_ = lean_ctor_get_uint8(v___x_1429_, 17);
v_zetaHave_1447_ = lean_ctor_get_uint8(v___x_1429_, 18);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1449_ = v___x_1429_;
v_isShared_1450_ = v_isSharedCheck_1506_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1429_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1506_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint8_t v_trackZetaDelta_1451_; lean_object* v_zetaDeltaSet_1452_; lean_object* v_lctx_1453_; lean_object* v_localInstances_1454_; lean_object* v_defEqCtx_x3f_1455_; lean_object* v_synthPendingDepth_1456_; lean_object* v_canUnfold_x3f_1457_; uint8_t v_univApprox_1458_; uint8_t v_inTypeClassResolution_1459_; uint8_t v_cacheInferType_1460_; uint8_t v___x_1461_; lean_object* v_config_1463_; 
v_trackZetaDelta_1451_ = lean_ctor_get_uint8(v___y_1422_, sizeof(void*)*7);
v_zetaDeltaSet_1452_ = lean_ctor_get(v___y_1422_, 1);
lean_inc(v_zetaDeltaSet_1452_);
v_lctx_1453_ = lean_ctor_get(v___y_1422_, 2);
lean_inc_ref(v_lctx_1453_);
v_localInstances_1454_ = lean_ctor_get(v___y_1422_, 3);
lean_inc_ref(v_localInstances_1454_);
v_defEqCtx_x3f_1455_ = lean_ctor_get(v___y_1422_, 4);
lean_inc(v_defEqCtx_x3f_1455_);
v_synthPendingDepth_1456_ = lean_ctor_get(v___y_1422_, 5);
lean_inc(v_synthPendingDepth_1456_);
v_canUnfold_x3f_1457_ = lean_ctor_get(v___y_1422_, 6);
lean_inc(v_canUnfold_x3f_1457_);
v_univApprox_1458_ = lean_ctor_get_uint8(v___y_1422_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1459_ = lean_ctor_get_uint8(v___y_1422_, sizeof(void*)*7 + 2);
v_cacheInferType_1460_ = lean_ctor_get_uint8(v___y_1422_, sizeof(void*)*7 + 3);
v___x_1461_ = 2;
if (v_isShared_1450_ == 0)
{
v_config_1463_ = v___x_1449_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 0, v_foApprox_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 1, v_ctxApprox_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 2, v_quasiPatternApprox_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 3, v_constApprox_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 4, v_isDefEqStuckEx_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 5, v_unificationHints_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 6, v_proofIrrelevance_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 7, v_assignSyntheticOpaque_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 8, v_offsetCnstrs_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 10, v_etaStruct_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 11, v_univApprox_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 12, v_iota_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 13, v_beta_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 14, v_proj_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 15, v_zeta_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 16, v_zetaDelta_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 17, v_zetaUnused_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, 18, v_zetaHave_1447_);
v_config_1463_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
uint64_t v___x_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1497_; 
lean_ctor_set_uint8(v_config_1463_, 9, v___x_1461_);
v___x_1464_ = l_Lean_Meta_Context_configKey(v___y_1422_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___y_1422_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1498_ = lean_ctor_get(v___y_1422_, 6);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v___y_1422_, 5);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v___y_1422_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v___y_1422_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v___y_1422_, 2);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v___y_1422_, 1);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v___y_1422_, 0);
lean_dec(v_unused_1504_);
v___x_1466_ = v___y_1422_;
v_isShared_1467_ = v_isSharedCheck_1497_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v___y_1422_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1497_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
uint64_t v___x_1468_; uint64_t v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v_key_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1468_ = 2ULL;
v___x_1469_ = lean_uint64_shift_right(v___x_1464_, v___x_1468_);
v___x_1470_ = l_Lean_Expr_mvarId_x21(v_a_1428_);
lean_dec(v_a_1428_);
v___x_1471_ = 1;
v___x_1472_ = lean_uint64_shift_left(v___x_1469_, v___x_1468_);
v___x_1473_ = lean_uint64_once(&l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0, &l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0);
v_key_1474_ = lean_uint64_lor(v___x_1472_, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1475_, 0, v_config_1463_);
lean_ctor_set_uint64(v___x_1475_, sizeof(void*)*1, v_key_1474_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1475_);
v___x_1477_ = v___x_1466_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_zetaDeltaSet_1452_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_lctx_1453_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_localInstances_1454_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v_defEqCtx_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1496_, 5, v_synthPendingDepth_1456_);
lean_ctor_set(v_reuseFailAlloc_1496_, 6, v_canUnfold_x3f_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1496_, sizeof(void*)*7, v_trackZetaDelta_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1496_, sizeof(void*)*7 + 1, v_univApprox_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1496_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1496_, sizeof(void*)*7 + 3, v_cacheInferType_1460_);
v___x_1477_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_MVarId_refl(v___x_1470_, v___x_1471_, v___x_1477_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec_ref(v___x_1477_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1487_);
v___x_1480_ = v___x_1478_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1478_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(v___x_1471_);
if (v_isShared_1481_ == 0)
{
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
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1478_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1478_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
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
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v___y_1422_);
v_a_1507_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1427_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1427_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_2362__boxed_1523_; lean_object* v_res_1524_; 
v___x_2362__boxed_1523_ = lean_unbox(v___x_1516_);
v_res_1524_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1515_, v___x_2362__boxed_1523_, v___x_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1525_, lean_object* v_e_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_e_1526_);
v___x_1533_ = 0;
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_box(v___x_1533_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1536_, 0, v___x_1532_);
lean_closure_set(v___f_1536_, 1, v___x_1535_);
lean_closure_set(v___f_1536_, 2, v___x_1534_);
v___x_1537_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1537_, 0, lean_box(0));
lean_closure_set(v___x_1537_, 1, v_mctx_1525_);
lean_closure_set(v___x_1537_, 2, v___f_1536_);
v___x_1538_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1537_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1538_) == 0)
{
return v___x_1538_;
}
else
{
lean_object* v_a_1539_; uint8_t v___y_1541_; uint8_t v___x_1551_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
v___x_1551_ = l_Lean_Exception_isInterrupt(v_a_1539_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; 
v___x_1552_ = l_Lean_Exception_isRuntime(v_a_1539_);
v___y_1541_ = v___x_1552_;
goto v___jp_1540_;
}
else
{
lean_dec(v_a_1539_);
v___y_1541_ = v___x_1551_;
goto v___jp_1540_;
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1550_);
v___x_1543_ = v___x_1538_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v___x_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_box(v___y_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1553_, lean_object* v_e_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1553_, v_e_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_result_1567_; lean_object* v_eNew_1568_; lean_object* v___x_1569_; 
v_result_1567_ = lean_ctor_get(v_r_1561_, 2);
lean_inc_ref(v_result_1567_);
lean_dec_ref(v_r_1561_);
v_eNew_1568_ = lean_ctor_get(v_result_1567_, 0);
lean_inc_ref(v_eNew_1568_);
lean_dec_ref(v_result_1567_);
v___x_1569_ = l_Lean_Meta_ppExpr(v_eNew_1568_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1580_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1574_ = l_Std_Format_defWidth;
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = l_Std_Format_pretty(v_a_1570_, v___x_1574_, v___x_1575_, v___x_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1576_);
v___x_1578_ = v___x_1572_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1581_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1569_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1569_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1596_){
_start:
{
switch(v_x_1596_)
{
case 0:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_unsigned_to_nat(0u);
return v___x_1597_;
}
case 1:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_unsigned_to_nat(1u);
return v___x_1598_;
}
default: 
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_unsigned_to_nat(2u);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1600_){
_start:
{
uint8_t v_x_boxed_1601_; lean_object* v_res_1602_; 
v_x_boxed_1601_ = lean_unbox(v_x_1600_);
v_res_1602_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1605_){
_start:
{
uint8_t v_x_4__boxed_1606_; lean_object* v_res_1607_; 
v_x_4__boxed_1606_ = lean_unbox(v_x_1605_);
v_res_1607_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1606_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1608_){
_start:
{
lean_inc(v_k_1608_);
return v_k_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1609_);
lean_dec(v_k_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1611_, lean_object* v_ctorIdx_1612_, uint8_t v_t_1613_, lean_object* v_h_1614_, lean_object* v_k_1615_){
_start:
{
lean_inc(v_k_1615_);
return v_k_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1616_, lean_object* v_ctorIdx_1617_, lean_object* v_t_1618_, lean_object* v_h_1619_, lean_object* v_k_1620_){
_start:
{
uint8_t v_t_boxed_1621_; lean_object* v_res_1622_; 
v_t_boxed_1621_ = lean_unbox(v_t_1618_);
v_res_1622_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1616_, v_ctorIdx_1617_, v_t_boxed_1621_, v_h_1619_, v_k_1620_);
lean_dec(v_k_1620_);
lean_dec(v_ctorIdx_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1623_){
_start:
{
lean_inc(v_none_1623_);
return v_none_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1624_);
lean_dec(v_none_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1626_, uint8_t v_t_1627_, lean_object* v_h_1628_, lean_object* v_none_1629_){
_start:
{
lean_inc(v_none_1629_);
return v_none_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_none_1633_){
_start:
{
uint8_t v_t_boxed_1634_; lean_object* v_res_1635_; 
v_t_boxed_1634_ = lean_unbox(v_t_1631_);
v_res_1635_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1630_, v_t_boxed_1634_, v_h_1632_, v_none_1633_);
lean_dec(v_none_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1636_){
_start:
{
lean_inc(v_assumption_1636_);
return v_assumption_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1637_);
lean_dec(v_assumption_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1639_, uint8_t v_t_1640_, lean_object* v_h_1641_, lean_object* v_assumption_1642_){
_start:
{
lean_inc(v_assumption_1642_);
return v_assumption_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1643_, lean_object* v_t_1644_, lean_object* v_h_1645_, lean_object* v_assumption_1646_){
_start:
{
uint8_t v_t_boxed_1647_; lean_object* v_res_1648_; 
v_t_boxed_1647_ = lean_unbox(v_t_1644_);
v_res_1648_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1643_, v_t_boxed_1647_, v_h_1645_, v_assumption_1646_);
lean_dec(v_assumption_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1649_){
_start:
{
lean_inc(v_solveByElim_1649_);
return v_solveByElim_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1650_);
lean_dec(v_solveByElim_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1652_, uint8_t v_t_1653_, lean_object* v_h_1654_, lean_object* v_solveByElim_1655_){
_start:
{
lean_inc(v_solveByElim_1655_);
return v_solveByElim_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1656_, lean_object* v_t_1657_, lean_object* v_h_1658_, lean_object* v_solveByElim_1659_){
_start:
{
uint8_t v_t_boxed_1660_; lean_object* v_res_1661_; 
v_t_boxed_1660_ = lean_unbox(v_t_1657_);
v_res_1661_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1656_, v_t_boxed_1660_, v_h_1658_, v_solveByElim_1659_);
lean_dec(v_solveByElim_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1671_, v_x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_x_1672_);
lean_dec(v_x_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = 0;
v___x_1686_ = lean_box(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_x_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v_env_1702_; lean_object* v___x_1703_; lean_object* v_mctx_1704_; lean_object* v_lctx_1705_; lean_object* v_options_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1701_ = lean_st_ref_get(v___y_1699_);
v_env_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_ref(v_env_1702_);
lean_dec(v___x_1701_);
v___x_1703_ = lean_st_ref_get(v___y_1697_);
v_mctx_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_mctx_1704_);
lean_dec(v___x_1703_);
v_lctx_1705_ = lean_ctor_get(v___y_1696_, 2);
v_options_1706_ = lean_ctor_get(v___y_1698_, 2);
lean_inc_ref(v_options_1706_);
lean_inc_ref(v_lctx_1705_);
v___x_1707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1707_, 0, v_env_1702_);
lean_ctor_set(v___x_1707_, 1, v_mctx_1704_);
lean_ctor_set(v___x_1707_, 2, v_lctx_1705_);
lean_ctor_set(v___x_1707_, 3, v_options_1706_);
v___x_1708_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v_msgData_1695_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_ref_1723_; lean_object* v___x_1724_; lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_ref_1723_ = lean_ctor_get(v___y_1720_, 5);
v___x_1724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_inc(v_ref_1723_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_ref_1723_);
lean_ctor_set(v___x_1729_, 1, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1743_ = l_Lean_stringToMessageData(v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1751_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1750_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v_x_1752_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1768_, lean_object* v_depth_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___f_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v_cfg_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___f_1775_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1776_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1777_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1778_ = 0;
v___x_1779_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1779_, 0, v_depth_1769_);
lean_ctor_set(v___x_1779_, 1, v___f_1775_);
lean_ctor_set(v___x_1779_, 2, v___f_1776_);
lean_ctor_set(v___x_1779_, 3, v___f_1777_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*4, v___x_1778_);
v___x_1780_ = 1;
v___x_1781_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1782_ = 1;
v___x_1783_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1783_, 0, v___x_1779_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*2, v___x_1782_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*2 + 1, v___x_1780_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*2 + 2, v___x_1778_);
v_cfg_1784_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1784_, 0, v___x_1783_);
lean_ctor_set_uint8(v_cfg_1784_, sizeof(void*)*1, v___x_1780_);
lean_ctor_set_uint8(v_cfg_1784_, sizeof(void*)*1 + 1, v___x_1780_);
lean_ctor_set_uint8(v_cfg_1784_, sizeof(void*)*1 + 2, v___x_1780_);
lean_ctor_set_uint8(v_cfg_1784_, sizeof(void*)*1 + 3, v___x_1778_);
v___x_1785_ = lean_box(0);
v___x_1786_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1787_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1778_, v___x_1778_, v___x_1785_, v___x_1785_, v___x_1786_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1791_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1787_);
v_fst_1789_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_fst_1789_);
v_snd_1790_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_snd_1790_);
lean_dec(v_a_1788_);
v___x_1791_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1784_, v_fst_1789_, v_snd_1790_, v_goals_1768_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1802_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
if (lean_obj_tag(v_a_1792_) == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = lean_box(0);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_del_object(v___x_1794_);
lean_dec(v_a_1792_);
v___x_1800_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1801_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1800_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
return v___x_1801_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1791_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1791_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_cfg_1784_);
lean_dec(v_goals_1768_);
v_a_1811_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1787_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1787_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1819_, lean_object* v_depth_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1819_, v_depth_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1827_, lean_object* v_msg_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1835_, v_msg_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_hasMVar(v_e_1843_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_e_1843_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_mctx_1849_; lean_object* v___x_1850_; lean_object* v_fst_1851_; lean_object* v_snd_1852_; lean_object* v___x_1853_; lean_object* v_cache_1854_; lean_object* v_zetaDeltaFVarIds_1855_; lean_object* v_postponed_1856_; lean_object* v_diag_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
v___x_1848_ = lean_st_ref_get(v___y_1844_);
v_mctx_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_mctx_1849_);
lean_dec(v___x_1848_);
v___x_1850_ = l_Lean_instantiateMVarsCore(v_mctx_1849_, v_e_1843_);
v_fst_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_fst_1851_);
v_snd_1852_ = lean_ctor_get(v___x_1850_, 1);
lean_inc(v_snd_1852_);
lean_dec_ref(v___x_1850_);
v___x_1853_ = lean_st_ref_take(v___y_1844_);
v_cache_1854_ = lean_ctor_get(v___x_1853_, 1);
v_zetaDeltaFVarIds_1855_ = lean_ctor_get(v___x_1853_, 2);
v_postponed_1856_ = lean_ctor_get(v___x_1853_, 3);
v_diag_1857_ = lean_ctor_get(v___x_1853_, 4);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1853_, 0);
lean_dec(v_unused_1867_);
v___x_1859_ = v___x_1853_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_diag_1857_);
lean_inc(v_postponed_1856_);
lean_inc(v_zetaDeltaFVarIds_1855_);
lean_inc(v_cache_1854_);
lean_dec(v___x_1853_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_snd_1852_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_snd_1852_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_cache_1854_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_zetaDeltaFVarIds_1855_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_postponed_1856_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_diag_1857_);
v___x_1862_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_st_ref_set(v___y_1844_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_fst_1851_);
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1872_, v___y_1874_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1886_; double v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_float_of_nat(v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1891_, lean_object* v_msg_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_ref_1898_; lean_object* v___x_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1944_; 
v_ref_1898_ = lean_ctor_get(v___y_1895_, 5);
v___x_1899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1944_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1944_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v_traceState_1905_; lean_object* v_env_1906_; lean_object* v_nextMacroScope_1907_; lean_object* v_ngen_1908_; lean_object* v_auxDeclNGen_1909_; lean_object* v_cache_1910_; lean_object* v_messages_1911_; lean_object* v_infoState_1912_; lean_object* v_snapshotTasks_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1943_; 
v___x_1904_ = lean_st_ref_take(v___y_1896_);
v_traceState_1905_ = lean_ctor_get(v___x_1904_, 4);
v_env_1906_ = lean_ctor_get(v___x_1904_, 0);
v_nextMacroScope_1907_ = lean_ctor_get(v___x_1904_, 1);
v_ngen_1908_ = lean_ctor_get(v___x_1904_, 2);
v_auxDeclNGen_1909_ = lean_ctor_get(v___x_1904_, 3);
v_cache_1910_ = lean_ctor_get(v___x_1904_, 5);
v_messages_1911_ = lean_ctor_get(v___x_1904_, 6);
v_infoState_1912_ = lean_ctor_get(v___x_1904_, 7);
v_snapshotTasks_1913_ = lean_ctor_get(v___x_1904_, 8);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1915_ = v___x_1904_;
v_isShared_1916_ = v_isSharedCheck_1943_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snapshotTasks_1913_);
lean_inc(v_infoState_1912_);
lean_inc(v_messages_1911_);
lean_inc(v_cache_1910_);
lean_inc(v_traceState_1905_);
lean_inc(v_auxDeclNGen_1909_);
lean_inc(v_ngen_1908_);
lean_inc(v_nextMacroScope_1907_);
lean_inc(v_env_1906_);
lean_dec(v___x_1904_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1943_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
uint64_t v_tid_1917_; lean_object* v_traces_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1942_; 
v_tid_1917_ = lean_ctor_get_uint64(v_traceState_1905_, sizeof(void*)*1);
v_traces_1918_ = lean_ctor_get(v_traceState_1905_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_traceState_1905_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1920_ = v_traceState_1905_;
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_traces_1918_);
lean_dec(v_traceState_1905_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; double v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1924_ = 0;
v___x_1925_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1926_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1926_, 0, v_cls_1891_);
lean_ctor_set(v___x_1926_, 1, v___x_1922_);
lean_ctor_set(v___x_1926_, 2, v___x_1925_);
lean_ctor_set_float(v___x_1926_, sizeof(void*)*3, v___x_1923_);
lean_ctor_set_float(v___x_1926_, sizeof(void*)*3 + 8, v___x_1923_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*3 + 16, v___x_1924_);
v___x_1927_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1928_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v_a_1900_);
lean_ctor_set(v___x_1928_, 2, v___x_1927_);
lean_inc(v_ref_1898_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_ref_1898_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_PersistentArray_push___redArg(v_traces_1918_, v___x_1929_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1930_);
v___x_1932_ = v___x_1920_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1930_);
lean_ctor_set_uint64(v_reuseFailAlloc_1941_, sizeof(void*)*1, v_tid_1917_);
v___x_1932_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 4, v___x_1932_);
v___x_1934_ = v___x_1915_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_env_1906_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_nextMacroScope_1907_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_ngen_1908_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_auxDeclNGen_1909_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v_cache_1910_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_messages_1911_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_infoState_1912_);
lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_snapshotTasks_1913_);
v___x_1934_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = lean_st_ref_set(v___y_1896_, v___x_1934_);
v___x_1936_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1936_);
v___x_1938_ = v___x_1902_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1945_, lean_object* v_msg_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1945_, v_msg_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = l_List_reverse___redArg(v_x_1954_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v_head_1962_; lean_object* v_tail_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1981_; 
v_head_1962_ = lean_ctor_get(v_x_1953_, 0);
v_tail_1963_ = lean_ctor_get(v_x_1953_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_x_1953_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1965_ = v_x_1953_;
v_isShared_1966_ = v_isSharedCheck_1981_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_tail_1963_);
lean_inc(v_head_1962_);
lean_dec(v_x_1953_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1981_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_MVarId_assumption(v_head_1962_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v_x_1954_);
lean_ctor_set(v___x_1965_, 0, v_a_1968_);
v___x_1970_ = v___x_1965_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1968_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_x_1954_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v_x_1953_ = v_tail_1963_;
v_x_1954_ = v___x_1970_;
goto _start;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_del_object(v___x_1965_);
lean_dec(v_tail_1963_);
lean_dec(v_x_1954_);
v_a_1973_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1967_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1967_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1982_, v_x_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2003_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_2004_ = l_Lean_Name_append(v___x_2003_, v___x_2002_);
return v___x_2004_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_2009_, lean_object* v_goal_2010_, lean_object* v_target_2011_, uint8_t v_symm_2012_, uint8_t v_side_2013_, lean_object* v_lem_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v_fst_2052_; uint8_t v_snd_2053_; lean_object* v___y_2077_; uint8_t v___y_2078_; lean_object* v___y_2079_; uint8_t v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2136_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v_val_2234_; 
if (lean_obj_tag(v_lem_2014_) == 0)
{
lean_object* v_val_2244_; 
v_val_2244_ = lean_ctor_get(v_lem_2014_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v_lem_2014_);
v_val_2234_ = v_val_2244_;
goto v___jp_2233_;
}
else
{
lean_object* v_val_2245_; lean_object* v___x_2246_; 
v_val_2245_ = lean_ctor_get(v_lem_2014_, 0);
lean_inc(v_val_2245_);
lean_dec_ref(v_lem_2014_);
v___x_2246_ = l_Lean_Meta_saveState___redArg(v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2245_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; 
lean_dec(v_a_2247_);
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2248_);
v_val_2234_ = v_a_2249_;
goto v___jp_2233_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_target_2011_);
lean_dec(v_goal_2010_);
lean_dec(v_weight_2009_);
v_a_2250_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2252_ = v___x_2248_;
v_isShared_2253_ = v_isSharedCheck_2279_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2248_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2279_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
uint8_t v___y_2255_; uint8_t v___x_2277_; 
v___x_2277_ = l_Lean_Exception_isInterrupt(v_a_2250_);
if (v___x_2277_ == 0)
{
uint8_t v___x_2278_; 
lean_inc(v_a_2250_);
v___x_2278_ = l_Lean_Exception_isRuntime(v_a_2250_);
v___y_2255_ = v___x_2278_;
goto v___jp_2254_;
}
else
{
v___y_2255_ = v___x_2277_;
goto v___jp_2254_;
}
v___jp_2254_:
{
if (v___y_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_del_object(v___x_2252_);
lean_dec(v_a_2250_);
v___x_2256_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2247_, v___y_2016_, v___y_2018_);
lean_dec(v_a_2247_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2264_; 
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2256_, 0);
lean_dec(v_unused_2265_);
v___x_2258_ = v___x_2256_;
v_isShared_2259_ = v_isSharedCheck_2264_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v___x_2256_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2264_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_box(0);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2260_);
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2256_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v___x_2275_; 
lean_dec(v_a_2247_);
if (v_isShared_2253_ == 0)
{
v___x_2275_ = v___x_2252_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2250_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_val_2245_);
lean_dec_ref(v_target_2011_);
lean_dec(v_goal_2010_);
lean_dec(v_weight_2009_);
v_a_2280_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2246_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2246_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2020_:
{
if (v___y_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec_ref(v___y_2021_);
v___x_2026_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2023_, v___y_2022_, v___y_2024_);
lean_dec_ref(v___y_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2034_; 
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v___x_2026_, 0);
lean_dec(v_unused_2035_);
v___x_2028_ = v___x_2026_;
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2026_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(0);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2030_);
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2026_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2026_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec_ref(v___y_2023_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2021_);
return v___x_2044_;
}
}
v___jp_2045_:
{
lean_object* v___x_2054_; lean_object* v_mctx_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_st_ref_get(v___y_2048_);
v_mctx_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref_n(v_mctx_2055_, 2);
lean_dec(v___x_2054_);
v___x_2056_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2055_, v___y_2046_, v___y_2051_, v___y_2048_, v___y_2047_, v___y_2050_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2067_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2061_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2061_, 0, v_fst_2052_);
lean_ctor_set(v___x_2061_, 1, v_weight_2009_);
lean_ctor_set(v___x_2061_, 2, v___y_2049_);
lean_ctor_set(v___x_2061_, 3, v_mctx_2055_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*4, v_snd_2053_);
v___x_2062_ = lean_unbox(v_a_2057_);
lean_dec(v_a_2057_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*4 + 1, v___x_2062_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2063_);
v___x_2065_ = v___x_2059_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_mctx_2055_);
lean_dec_ref(v_fst_2052_);
lean_dec_ref(v___y_2049_);
lean_dec(v_weight_2009_);
v_a_2068_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2056_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2056_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
v___jp_2076_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2079_);
if (lean_obj_tag(v___x_2085_) == 1)
{
lean_object* v_val_2086_; lean_object* v___x_2087_; lean_object* v_a_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_val_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_val_2086_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2086_, v___y_2082_);
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2090_ = lean_unsigned_to_nat(4u);
v___x_2091_ = l_Lean_Expr_isAppOfArity(v_a_2088_, v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
v___y_2046_ = v___y_2077_;
v___y_2047_ = v___y_2083_;
v___y_2048_ = v___y_2082_;
v___y_2049_ = v___y_2079_;
v___y_2050_ = v___y_2084_;
v___y_2051_ = v___y_2081_;
v_fst_2052_ = v_a_2088_;
v_snd_2053_ = v___y_2078_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2092_ = lean_unsigned_to_nat(3u);
v___x_2093_ = l_Lean_Expr_getAppNumArgs(v_a_2088_);
v___x_2094_ = lean_nat_sub(v___x_2093_, v___x_2092_);
lean_dec(v___x_2093_);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_sub(v___x_2094_, v___x_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = l_Lean_Expr_getRevArg_x21(v_a_2088_, v___x_2096_);
lean_dec(v_a_2088_);
v___y_2046_ = v___y_2077_;
v___y_2047_ = v___y_2083_;
v___y_2048_ = v___y_2082_;
v___y_2049_ = v___y_2079_;
v___y_2050_ = v___y_2084_;
v___y_2051_ = v___y_2081_;
v_fst_2052_ = v___x_2097_;
v_snd_2053_ = v___y_2080_;
goto v___jp_2045_;
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v___x_2085_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v___y_2077_);
lean_dec(v_weight_2009_);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
v___jp_2100_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
v___jp_2103_:
{
if (v___y_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v___y_2106_);
v___x_2109_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2107_, v___y_2104_, v___y_2105_);
lean_dec_ref(v___y_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec_ref(v___x_2109_);
goto v___jp_2100_;
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
lean_ctor_set(v___x_2118_, 0, v___y_2106_);
return v___x_2118_;
}
}
v___jp_2119_:
{
if (v___y_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v___y_2123_);
v___x_2125_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec_ref(v___y_2120_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_dec_ref(v___x_2125_);
goto v___jp_2100_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2134_; 
lean_dec_ref(v___y_2120_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___y_2123_);
return v___x_2134_;
}
}
v___jp_2135_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_Meta_saveState___redArg(v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = 1;
v___x_2140_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2136_);
v___x_2141_ = l_Lean_MVarId_rewrite(v_goal_2010_, v_target_2011_, v___y_2136_, v_symm_2012_, v___x_2140_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v_a_2138_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2203_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2203_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_eNew_2146_; lean_object* v_mvarIds_2147_; uint8_t v___x_2148_; 
v_eNew_2146_ = lean_ctor_get(v_a_2142_, 0);
v_mvarIds_2147_ = lean_ctor_get(v_a_2142_, 2);
v___x_2148_ = l_List_isEmpty___redArg(v_mvarIds_2147_);
if (v___x_2148_ == 0)
{
lean_inc_ref(v_eNew_2146_);
lean_del_object(v___x_2144_);
lean_dec_ref(v___y_2136_);
switch(v_side_2013_)
{
case 0:
{
if (v___x_2148_ == 0)
{
lean_dec_ref(v_eNew_2146_);
lean_dec(v_a_2142_);
lean_dec(v_weight_2009_);
goto v___jp_2100_;
}
else
{
v___y_2077_ = v_eNew_2146_;
v___y_2078_ = v___x_2148_;
v___y_2079_ = v_a_2142_;
v___y_2080_ = v___x_2139_;
v___y_2081_ = v___y_2015_;
v___y_2082_ = v___y_2016_;
v___y_2083_ = v___y_2017_;
v___y_2084_ = v___y_2018_;
goto v___jp_2076_;
}
}
case 1:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Meta_saveState___redArg(v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
v___x_2151_ = lean_box(0);
lean_inc(v_mvarIds_2147_);
v___x_2152_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2147_, v___x_2151_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_dec_ref(v___x_2152_);
lean_dec(v_a_2150_);
v___y_2077_ = v_eNew_2146_;
v___y_2078_ = v___x_2148_;
v___y_2079_ = v_a_2142_;
v___y_2080_ = v___x_2139_;
v___y_2081_ = v___y_2015_;
v___y_2082_ = v___y_2016_;
v___y_2083_ = v___y_2017_;
v___y_2084_ = v___y_2018_;
goto v___jp_2076_;
}
else
{
lean_object* v_a_2153_; uint8_t v___x_2154_; 
lean_dec_ref(v_eNew_2146_);
lean_dec(v_a_2142_);
lean_dec(v_weight_2009_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l_Lean_Exception_isInterrupt(v_a_2153_);
if (v___x_2154_ == 0)
{
uint8_t v___x_2155_; 
lean_inc(v_a_2153_);
v___x_2155_ = l_Lean_Exception_isRuntime(v_a_2153_);
v___y_2120_ = v_a_2150_;
v___y_2121_ = v___y_2016_;
v___y_2122_ = v___y_2018_;
v___y_2123_ = v_a_2153_;
v___y_2124_ = v___x_2155_;
goto v___jp_2119_;
}
else
{
v___y_2120_ = v_a_2150_;
v___y_2121_ = v___y_2016_;
v___y_2122_ = v___y_2018_;
v___y_2123_ = v_a_2153_;
v___y_2124_ = v___x_2154_;
goto v___jp_2119_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_eNew_2146_);
lean_dec(v_a_2142_);
lean_dec(v_weight_2009_);
v_a_2156_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2149_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2149_);
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
default: 
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Meta_saveState___redArg(v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2147_);
v___x_2167_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2147_, v___x_2166_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_dec_ref(v___x_2167_);
lean_dec(v_a_2165_);
v___y_2077_ = v_eNew_2146_;
v___y_2078_ = v___x_2148_;
v___y_2079_ = v_a_2142_;
v___y_2080_ = v___x_2139_;
v___y_2081_ = v___y_2015_;
v___y_2082_ = v___y_2016_;
v___y_2083_ = v___y_2017_;
v___y_2084_ = v___y_2018_;
goto v___jp_2076_;
}
else
{
lean_object* v_a_2168_; uint8_t v___x_2169_; 
lean_dec_ref(v_eNew_2146_);
lean_dec(v_a_2142_);
lean_dec(v_weight_2009_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = l_Lean_Exception_isInterrupt(v_a_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; 
lean_inc(v_a_2168_);
v___x_2170_ = l_Lean_Exception_isRuntime(v_a_2168_);
v___y_2104_ = v___y_2016_;
v___y_2105_ = v___y_2018_;
v___y_2106_ = v_a_2168_;
v___y_2107_ = v_a_2165_;
v___y_2108_ = v___x_2170_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2016_;
v___y_2105_ = v___y_2018_;
v___y_2106_ = v_a_2168_;
v___y_2107_ = v_a_2165_;
v___y_2108_ = v___x_2169_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_eNew_2146_);
lean_dec(v_a_2142_);
lean_dec(v_weight_2009_);
v_a_2171_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2164_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2164_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v_mctx_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_st_ref_get(v___y_2016_);
v_mctx_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_ref_n(v_mctx_2180_, 2);
lean_dec(v___x_2179_);
lean_inc_ref(v_eNew_2146_);
v___x_2181_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2180_, v_eNew_2146_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2194_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2186_, 0, v___y_2136_);
lean_ctor_set(v___x_2186_, 1, v_weight_2009_);
lean_ctor_set(v___x_2186_, 2, v_a_2142_);
lean_ctor_set(v___x_2186_, 3, v_mctx_2180_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*4, v_symm_2012_);
v___x_2187_ = lean_unbox(v_a_2182_);
lean_dec(v_a_2182_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*4 + 1, v___x_2187_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 1);
lean_ctor_set(v___x_2144_, 0, v___x_2186_);
v___x_2189_ = v___x_2144_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2186_);
v___x_2189_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2189_);
v___x_2191_ = v___x_2184_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
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
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_mctx_2180_);
lean_del_object(v___x_2144_);
lean_dec(v_a_2142_);
lean_dec_ref(v___y_2136_);
lean_dec(v_weight_2009_);
v_a_2195_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2181_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2181_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
else
{
lean_object* v_a_2204_; uint8_t v___x_2205_; 
lean_dec_ref(v___y_2136_);
lean_dec(v_weight_2009_);
v_a_2204_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2141_);
v___x_2205_ = l_Lean_Exception_isInterrupt(v_a_2204_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; 
lean_inc(v_a_2204_);
v___x_2206_ = l_Lean_Exception_isRuntime(v_a_2204_);
v___y_2021_ = v_a_2204_;
v___y_2022_ = v___y_2016_;
v___y_2023_ = v_a_2138_;
v___y_2024_ = v___y_2018_;
v___y_2025_ = v___x_2206_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v_a_2204_;
v___y_2022_ = v___y_2016_;
v___y_2023_ = v_a_2138_;
v___y_2024_ = v___y_2018_;
v___y_2025_ = v___x_2205_;
goto v___jp_2020_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v___y_2136_);
lean_dec_ref(v_target_2011_);
lean_dec(v_goal_2010_);
lean_dec(v_weight_2009_);
v_a_2207_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2137_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2137_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
v___jp_2215_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_inc_ref(v___y_2219_);
v___x_2220_ = l_Lean_stringToMessageData(v___y_2219_);
lean_inc_ref(v___y_2218_);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___y_2218_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
lean_inc_ref(v___y_2217_);
v___x_2222_ = l_Lean_MessageData_ofExpr(v___y_2217_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
lean_inc(v___y_2216_);
v___x_2224_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2216_, v___x_2223_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_dec_ref(v___x_2224_);
v___y_2136_ = v___y_2217_;
goto v___jp_2135_;
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_target_2011_);
lean_dec(v_goal_2010_);
lean_dec(v_weight_2009_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
v___jp_2233_:
{
lean_object* v_options_2235_; uint8_t v_hasTrace_2236_; 
v_options_2235_ = lean_ctor_get(v___y_2017_, 2);
v_hasTrace_2236_ = lean_ctor_get_uint8(v_options_2235_, sizeof(void*)*1);
if (v_hasTrace_2236_ == 0)
{
v___y_2136_ = v_val_2234_;
goto v___jp_2135_;
}
else
{
lean_object* v_inheritedTraceOptions_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_inheritedTraceOptions_2237_ = lean_ctor_get(v___y_2017_, 13);
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2239_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2237_, v_options_2235_, v___x_2239_);
if (v___x_2240_ == 0)
{
v___y_2136_ = v_val_2234_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_2012_ == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2216_ = v___x_2238_;
v___y_2217_ = v_val_2234_;
v___y_2218_ = v___x_2241_;
v___y_2219_ = v___x_2242_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2216_ = v___x_2238_;
v___y_2217_ = v_val_2234_;
v___y_2218_ = v___x_2241_;
v___y_2219_ = v___x_2243_;
goto v___jp_2215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2288_, lean_object* v_goal_2289_, lean_object* v_target_2290_, lean_object* v_symm_2291_, lean_object* v_side_2292_, lean_object* v_lem_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_symm_boxed_2299_; uint8_t v_side_boxed_2300_; lean_object* v_res_2301_; 
v_symm_boxed_2299_ = lean_unbox(v_symm_2291_);
v_side_boxed_2300_ = lean_unbox(v_side_2292_);
v_res_2301_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2288_, v_goal_2289_, v_target_2290_, v_symm_boxed_2299_, v_side_boxed_2300_, v_lem_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2302_, lean_object* v_goal_2303_, lean_object* v_target_2304_, uint8_t v_side_2305_, lean_object* v_lem_2306_, uint8_t v_symm_2307_, lean_object* v_weight_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_box(v_symm_2307_);
v___x_2315_ = lean_box(v_side_2305_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2316_, 0, v_weight_2308_);
lean_closure_set(v___f_2316_, 1, v_goal_2303_);
lean_closure_set(v___f_2316_, 2, v_target_2304_);
lean_closure_set(v___f_2316_, 3, v___x_2314_);
lean_closure_set(v___f_2316_, 4, v___x_2315_);
lean_closure_set(v___f_2316_, 5, v_lem_2306_);
v___x_2317_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2302_, v___f_2316_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2318_, lean_object* v_goal_2319_, lean_object* v_target_2320_, lean_object* v_side_2321_, lean_object* v_lem_2322_, lean_object* v_symm_2323_, lean_object* v_weight_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v_side_boxed_2330_; uint8_t v_symm_boxed_2331_; lean_object* v_res_2332_; 
v_side_boxed_2330_ = lean_unbox(v_side_2321_);
v_symm_boxed_2331_ = lean_unbox(v_symm_2323_);
v_res_2332_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2318_, v_goal_2319_, v_target_2320_, v_side_boxed_2330_, v_lem_2322_, v_symm_boxed_2331_, v_weight_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2333_, lean_object* v_k_2334_, uint8_t v_cleanupAnnotations_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___f_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2341_, 0, v_k_2334_);
v___x_2342_ = 0;
v___x_2343_ = lean_box(0);
v___x_2344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2342_, v___x_2343_, v_type_2333_, v___f_2341_, v_cleanupAnnotations_2335_, v___x_2342_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2344_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2344_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2361_, lean_object* v_k_2362_, lean_object* v_cleanupAnnotations_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2369_; lean_object* v_res_2370_; 
v_cleanupAnnotations_boxed_2369_ = lean_unbox(v_cleanupAnnotations_2363_);
v_res_2370_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2361_, v_k_2362_, v_cleanupAnnotations_boxed_2369_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2371_, lean_object* v_type_2372_, lean_object* v_k_2373_, uint8_t v_cleanupAnnotations_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2372_, v_k_2373_, v_cleanupAnnotations_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2381_, lean_object* v_type_2382_, lean_object* v_k_2383_, lean_object* v_cleanupAnnotations_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2390_; lean_object* v_res_2391_; 
v_cleanupAnnotations_boxed_2390_ = lean_unbox(v_cleanupAnnotations_2384_);
v_res_2391_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2381_, v_type_2382_, v_k_2383_, v_cleanupAnnotations_boxed_2390_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2392_, lean_object* v_k_2393_, uint8_t v_cleanupAnnotations_2394_, uint8_t v_preserveNondepLet_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___f_2401_; uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2401_, 0, v_k_2393_);
v___x_2402_ = 1;
v___x_2403_ = 0;
v___x_2404_ = lean_box(0);
v___x_2405_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2392_, v___x_2402_, v___x_2402_, v_preserveNondepLet_2395_, v___x_2403_, v___x_2404_, v___f_2401_, v_cleanupAnnotations_2394_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
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
v_a_2414_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2405_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2405_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2422_, lean_object* v_k_2423_, lean_object* v_cleanupAnnotations_2424_, lean_object* v_preserveNondepLet_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2431_; uint8_t v_preserveNondepLet_boxed_2432_; lean_object* v_res_2433_; 
v_cleanupAnnotations_boxed_2431_ = lean_unbox(v_cleanupAnnotations_2424_);
v_preserveNondepLet_boxed_2432_ = lean_unbox(v_preserveNondepLet_2425_);
v_res_2433_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2422_, v_k_2423_, v_cleanupAnnotations_boxed_2431_, v_preserveNondepLet_boxed_2432_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2434_, lean_object* v_e_2435_, lean_object* v_k_2436_, uint8_t v_cleanupAnnotations_2437_, uint8_t v_preserveNondepLet_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2435_, v_k_2436_, v_cleanupAnnotations_2437_, v_preserveNondepLet_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_e_2446_, lean_object* v_k_2447_, lean_object* v_cleanupAnnotations_2448_, lean_object* v_preserveNondepLet_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2455_; uint8_t v_preserveNondepLet_boxed_2456_; lean_object* v_res_2457_; 
v_cleanupAnnotations_boxed_2455_ = lean_unbox(v_cleanupAnnotations_2448_);
v_preserveNondepLet_boxed_2456_ = lean_unbox(v_preserveNondepLet_2449_);
v_res_2457_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2445_, v_e_2446_, v_k_2447_, v_cleanupAnnotations_boxed_2455_, v_preserveNondepLet_boxed_2456_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2458_, lean_object* v_e_x27_2459_, lean_object* v_a_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc_ref(v_e_x27_2459_);
v___x_2466_ = lean_apply_7(v_f_2458_, v_a_2460_, v_e_x27_2459_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, lean_box(0));
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2475_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_e_x27_2459_);
lean_ctor_set(v___x_2471_, 1, v_a_2467_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2471_);
v___x_2473_ = v___x_2469_;
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
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_e_x27_2459_);
v_a_2476_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2466_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2466_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2484_, lean_object* v_e_x27_2485_, lean_object* v_a_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2484_, v_e_x27_2485_, v_a_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
switch(lean_obj_tag(v_x_2494_))
{
case 7:
{
lean_object* v_binderName_2501_; lean_object* v_binderType_2502_; lean_object* v_body_2503_; uint8_t v_binderInfo_2504_; lean_object* v___x_2505_; 
v_binderName_2501_ = lean_ctor_get(v_x_2494_, 0);
v_binderType_2502_ = lean_ctor_get(v_x_2494_, 1);
v_body_2503_ = lean_ctor_get(v_x_2494_, 2);
v_binderInfo_2504_ = lean_ctor_get_uint8(v_x_2494_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2502_);
lean_inc_ref(v_f_2493_);
v___x_2505_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_binderType_2502_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___x_2509_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v_fst_2507_ = lean_ctor_get(v_a_2506_, 0);
lean_inc(v_fst_2507_);
v_snd_2508_ = lean_ctor_get(v_a_2506_, 1);
lean_inc(v_snd_2508_);
lean_dec(v_a_2506_);
lean_inc_ref(v_body_2503_);
v___x_2509_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_body_2503_, v_snd_2508_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2539_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2539_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2539_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_fst_2514_; lean_object* v_snd_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2538_; 
v_fst_2514_ = lean_ctor_get(v_a_2510_, 0);
v_snd_2515_ = lean_ctor_get(v_a_2510_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2510_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2517_ = v_a_2510_;
v_isShared_2518_ = v_isSharedCheck_2538_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_snd_2515_);
lean_inc(v_fst_2514_);
lean_dec(v_a_2510_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2538_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___y_2520_; uint8_t v___y_2528_; size_t v___x_2532_; size_t v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = lean_ptr_addr(v_binderType_2502_);
v___x_2533_ = lean_ptr_addr(v_fst_2507_);
v___x_2534_ = lean_usize_dec_eq(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
v___y_2528_ = v___x_2534_;
goto v___jp_2527_;
}
else
{
size_t v___x_2535_; size_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_ptr_addr(v_body_2503_);
v___x_2536_ = lean_ptr_addr(v_fst_2514_);
v___x_2537_ = lean_usize_dec_eq(v___x_2535_, v___x_2536_);
v___y_2528_ = v___x_2537_;
goto v___jp_2527_;
}
v___jp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___y_2520_);
v___x_2522_ = v___x_2517_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___y_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_snd_2515_);
v___x_2522_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2522_);
v___x_2524_ = v___x_2512_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
v___jp_2527_:
{
if (v___y_2528_ == 0)
{
lean_object* v___x_2529_; 
lean_inc(v_binderName_2501_);
lean_dec_ref(v_x_2494_);
v___x_2529_ = l_Lean_Expr_forallE___override(v_binderName_2501_, v_fst_2507_, v_fst_2514_, v_binderInfo_2504_);
v___y_2520_ = v___x_2529_;
goto v___jp_2519_;
}
else
{
uint8_t v___x_2530_; 
v___x_2530_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2504_, v_binderInfo_2504_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_inc(v_binderName_2501_);
lean_dec_ref(v_x_2494_);
v___x_2531_ = l_Lean_Expr_forallE___override(v_binderName_2501_, v_fst_2507_, v_fst_2514_, v_binderInfo_2504_);
v___y_2520_ = v___x_2531_;
goto v___jp_2519_;
}
else
{
lean_dec(v_fst_2514_);
lean_dec(v_fst_2507_);
v___y_2520_ = v_x_2494_;
goto v___jp_2519_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2507_);
lean_dec_ref(v_x_2494_);
return v___x_2509_;
}
}
else
{
lean_dec_ref(v_x_2494_);
lean_dec_ref(v_f_2493_);
return v___x_2505_;
}
}
case 6:
{
lean_object* v_binderName_2540_; lean_object* v_binderType_2541_; lean_object* v_body_2542_; uint8_t v_binderInfo_2543_; lean_object* v___x_2544_; 
v_binderName_2540_ = lean_ctor_get(v_x_2494_, 0);
v_binderType_2541_ = lean_ctor_get(v_x_2494_, 1);
v_body_2542_ = lean_ctor_get(v_x_2494_, 2);
v_binderInfo_2543_ = lean_ctor_get_uint8(v_x_2494_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2541_);
lean_inc_ref(v_f_2493_);
v___x_2544_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_binderType_2541_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_fst_2546_; lean_object* v_snd_2547_; lean_object* v___x_2548_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v_fst_2546_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_fst_2546_);
v_snd_2547_ = lean_ctor_get(v_a_2545_, 1);
lean_inc(v_snd_2547_);
lean_dec(v_a_2545_);
lean_inc_ref(v_body_2542_);
v___x_2548_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_body_2542_, v_snd_2547_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2578_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2578_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2578_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2553_; lean_object* v_snd_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2577_; 
v_fst_2553_ = lean_ctor_get(v_a_2549_, 0);
v_snd_2554_ = lean_ctor_get(v_a_2549_, 1);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2556_ = v_a_2549_;
v_isShared_2557_ = v_isSharedCheck_2577_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_snd_2554_);
lean_inc(v_fst_2553_);
lean_dec(v_a_2549_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2577_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___y_2559_; uint8_t v___y_2567_; size_t v___x_2571_; size_t v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = lean_ptr_addr(v_binderType_2541_);
v___x_2572_ = lean_ptr_addr(v_fst_2546_);
v___x_2573_ = lean_usize_dec_eq(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
v___y_2567_ = v___x_2573_;
goto v___jp_2566_;
}
else
{
size_t v___x_2574_; size_t v___x_2575_; uint8_t v___x_2576_; 
v___x_2574_ = lean_ptr_addr(v_body_2542_);
v___x_2575_ = lean_ptr_addr(v_fst_2553_);
v___x_2576_ = lean_usize_dec_eq(v___x_2574_, v___x_2575_);
v___y_2567_ = v___x_2576_;
goto v___jp_2566_;
}
v___jp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___y_2559_);
v___x_2561_ = v___x_2556_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___y_2559_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_snd_2554_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2563_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2561_);
v___x_2563_ = v___x_2551_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
v___jp_2566_:
{
if (v___y_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_inc(v_binderName_2540_);
lean_dec_ref(v_x_2494_);
v___x_2568_ = l_Lean_Expr_lam___override(v_binderName_2540_, v_fst_2546_, v_fst_2553_, v_binderInfo_2543_);
v___y_2559_ = v___x_2568_;
goto v___jp_2558_;
}
else
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2543_, v_binderInfo_2543_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_inc(v_binderName_2540_);
lean_dec_ref(v_x_2494_);
v___x_2570_ = l_Lean_Expr_lam___override(v_binderName_2540_, v_fst_2546_, v_fst_2553_, v_binderInfo_2543_);
v___y_2559_ = v___x_2570_;
goto v___jp_2558_;
}
else
{
lean_dec(v_fst_2553_);
lean_dec(v_fst_2546_);
v___y_2559_ = v_x_2494_;
goto v___jp_2558_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2546_);
lean_dec_ref(v_x_2494_);
return v___x_2548_;
}
}
else
{
lean_dec_ref(v_x_2494_);
lean_dec_ref(v_f_2493_);
return v___x_2544_;
}
}
case 10:
{
lean_object* v_data_2579_; lean_object* v_expr_2580_; lean_object* v___x_2581_; 
v_data_2579_ = lean_ctor_get(v_x_2494_, 0);
v_expr_2580_ = lean_ctor_get(v_x_2494_, 1);
lean_inc_ref(v_expr_2580_);
v___x_2581_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_expr_2580_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2604_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2604_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2604_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2603_; 
v_fst_2586_ = lean_ctor_get(v_a_2582_, 0);
v_snd_2587_ = lean_ctor_get(v_a_2582_, 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_a_2582_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2589_ = v_a_2582_;
v_isShared_2590_ = v_isSharedCheck_2603_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_inc(v_fst_2586_);
lean_dec(v_a_2582_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2603_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___y_2592_; size_t v___x_2599_; size_t v___x_2600_; uint8_t v___x_2601_; 
v___x_2599_ = lean_ptr_addr(v_expr_2580_);
v___x_2600_ = lean_ptr_addr(v_fst_2586_);
v___x_2601_ = lean_usize_dec_eq(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_inc(v_data_2579_);
lean_dec_ref(v_x_2494_);
v___x_2602_ = l_Lean_Expr_mdata___override(v_data_2579_, v_fst_2586_);
v___y_2592_ = v___x_2602_;
goto v___jp_2591_;
}
else
{
lean_dec(v_fst_2586_);
v___y_2592_ = v_x_2494_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___y_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___y_2592_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_snd_2587_);
v___x_2594_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2594_);
v___x_2596_ = v___x_2584_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_2494_);
return v___x_2581_;
}
}
case 8:
{
lean_object* v_declName_2605_; lean_object* v_type_2606_; lean_object* v_value_2607_; lean_object* v_body_2608_; uint8_t v_nondep_2609_; lean_object* v___x_2610_; 
v_declName_2605_ = lean_ctor_get(v_x_2494_, 0);
v_type_2606_ = lean_ctor_get(v_x_2494_, 1);
v_value_2607_ = lean_ctor_get(v_x_2494_, 2);
v_body_2608_ = lean_ctor_get(v_x_2494_, 3);
v_nondep_2609_ = lean_ctor_get_uint8(v_x_2494_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2606_);
lean_inc_ref(v_f_2493_);
v___x_2610_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_type_2606_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v_fst_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_fst_2612_);
v_snd_2613_ = lean_ctor_get(v_a_2611_, 1);
lean_inc(v_snd_2613_);
lean_dec(v_a_2611_);
lean_inc_ref(v_value_2607_);
lean_inc_ref(v_f_2493_);
v___x_2614_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_value_2607_, v_snd_2613_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2618_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v_fst_2616_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_a_2615_, 1);
lean_inc(v_snd_2617_);
lean_dec(v_a_2615_);
lean_inc_ref(v_body_2608_);
v___x_2618_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_body_2608_, v_snd_2617_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2650_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2650_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2650_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2649_; 
v_fst_2623_ = lean_ctor_get(v_a_2619_, 0);
v_snd_2624_ = lean_ctor_get(v_a_2619_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2626_ = v_a_2619_;
v_isShared_2627_ = v_isSharedCheck_2649_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2624_);
lean_inc(v_fst_2623_);
lean_dec(v_a_2619_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2649_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___y_2629_; uint8_t v___y_2637_; size_t v___x_2643_; size_t v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = lean_ptr_addr(v_type_2606_);
v___x_2644_ = lean_ptr_addr(v_fst_2612_);
v___x_2645_ = lean_usize_dec_eq(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2637_ = v___x_2645_;
goto v___jp_2636_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; uint8_t v___x_2648_; 
v___x_2646_ = lean_ptr_addr(v_value_2607_);
v___x_2647_ = lean_ptr_addr(v_fst_2616_);
v___x_2648_ = lean_usize_dec_eq(v___x_2646_, v___x_2647_);
v___y_2637_ = v___x_2648_;
goto v___jp_2636_;
}
v___jp_2628_:
{
lean_object* v___x_2631_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___y_2629_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___y_2629_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_snd_2624_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2631_);
v___x_2633_ = v___x_2621_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
v___jp_2636_:
{
if (v___y_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_inc(v_declName_2605_);
lean_dec_ref(v_x_2494_);
v___x_2638_ = l_Lean_Expr_letE___override(v_declName_2605_, v_fst_2612_, v_fst_2616_, v_fst_2623_, v_nondep_2609_);
v___y_2629_ = v___x_2638_;
goto v___jp_2628_;
}
else
{
size_t v___x_2639_; size_t v___x_2640_; uint8_t v___x_2641_; 
v___x_2639_ = lean_ptr_addr(v_body_2608_);
v___x_2640_ = lean_ptr_addr(v_fst_2623_);
v___x_2641_ = lean_usize_dec_eq(v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; 
lean_inc(v_declName_2605_);
lean_dec_ref(v_x_2494_);
v___x_2642_ = l_Lean_Expr_letE___override(v_declName_2605_, v_fst_2612_, v_fst_2616_, v_fst_2623_, v_nondep_2609_);
v___y_2629_ = v___x_2642_;
goto v___jp_2628_;
}
else
{
lean_dec(v_fst_2623_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2612_);
v___y_2629_ = v_x_2494_;
goto v___jp_2628_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2616_);
lean_dec(v_fst_2612_);
lean_dec_ref(v_x_2494_);
return v___x_2618_;
}
}
else
{
lean_dec(v_fst_2612_);
lean_dec_ref(v_x_2494_);
lean_dec_ref(v_f_2493_);
return v___x_2614_;
}
}
else
{
lean_dec_ref(v_x_2494_);
lean_dec_ref(v_f_2493_);
return v___x_2610_;
}
}
case 5:
{
lean_object* v_fn_2651_; lean_object* v_arg_2652_; lean_object* v___x_2653_; 
v_fn_2651_ = lean_ctor_get(v_x_2494_, 0);
v_arg_2652_ = lean_ctor_get(v_x_2494_, 1);
lean_inc_ref(v_fn_2651_);
lean_inc_ref(v_f_2493_);
v___x_2653_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_fn_2651_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2657_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2653_);
v_fst_2655_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_fst_2655_);
v_snd_2656_ = lean_ctor_get(v_a_2654_, 1);
lean_inc(v_snd_2656_);
lean_dec(v_a_2654_);
lean_inc_ref(v_arg_2652_);
v___x_2657_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_arg_2652_, v_snd_2656_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2685_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2685_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2685_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2684_; 
v_fst_2662_ = lean_ctor_get(v_a_2658_, 0);
v_snd_2663_ = lean_ctor_get(v_a_2658_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_a_2658_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2665_ = v_a_2658_;
v_isShared_2666_ = v_isSharedCheck_2684_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_inc(v_fst_2662_);
lean_dec(v_a_2658_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2684_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___y_2668_; uint8_t v___y_2676_; size_t v___x_2678_; size_t v___x_2679_; uint8_t v___x_2680_; 
v___x_2678_ = lean_ptr_addr(v_fn_2651_);
v___x_2679_ = lean_ptr_addr(v_fst_2655_);
v___x_2680_ = lean_usize_dec_eq(v___x_2678_, v___x_2679_);
if (v___x_2680_ == 0)
{
v___y_2676_ = v___x_2680_;
goto v___jp_2675_;
}
else
{
size_t v___x_2681_; size_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2681_ = lean_ptr_addr(v_arg_2652_);
v___x_2682_ = lean_ptr_addr(v_fst_2662_);
v___x_2683_ = lean_usize_dec_eq(v___x_2681_, v___x_2682_);
v___y_2676_ = v___x_2683_;
goto v___jp_2675_;
}
v___jp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___y_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___y_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_snd_2663_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2670_);
v___x_2672_ = v___x_2660_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
v___jp_2675_:
{
if (v___y_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref(v_x_2494_);
v___x_2677_ = l_Lean_Expr_app___override(v_fst_2655_, v_fst_2662_);
v___y_2668_ = v___x_2677_;
goto v___jp_2667_;
}
else
{
lean_dec(v_fst_2662_);
lean_dec(v_fst_2655_);
v___y_2668_ = v_x_2494_;
goto v___jp_2667_;
}
}
}
}
}
else
{
lean_dec(v_fst_2655_);
lean_dec_ref(v_x_2494_);
return v___x_2657_;
}
}
else
{
lean_dec_ref(v_x_2494_);
lean_dec_ref(v_f_2493_);
return v___x_2653_;
}
}
case 11:
{
lean_object* v_typeName_2686_; lean_object* v_idx_2687_; lean_object* v_struct_2688_; lean_object* v___x_2689_; 
v_typeName_2686_ = lean_ctor_get(v_x_2494_, 0);
v_idx_2687_ = lean_ctor_get(v_x_2494_, 1);
v_struct_2688_ = lean_ctor_get(v_x_2494_, 2);
lean_inc_ref(v_struct_2688_);
v___x_2689_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2493_, v_struct_2688_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2712_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2712_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2712_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2711_; 
v_fst_2694_ = lean_ctor_get(v_a_2690_, 0);
v_snd_2695_ = lean_ctor_get(v_a_2690_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_a_2690_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2697_ = v_a_2690_;
v_isShared_2698_ = v_isSharedCheck_2711_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_inc(v_fst_2694_);
lean_dec(v_a_2690_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2711_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___y_2700_; size_t v___x_2707_; size_t v___x_2708_; uint8_t v___x_2709_; 
v___x_2707_ = lean_ptr_addr(v_struct_2688_);
v___x_2708_ = lean_ptr_addr(v_fst_2694_);
v___x_2709_ = lean_usize_dec_eq(v___x_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_inc(v_idx_2687_);
lean_inc(v_typeName_2686_);
lean_dec_ref(v_x_2494_);
v___x_2710_ = l_Lean_Expr_proj___override(v_typeName_2686_, v_idx_2687_, v_fst_2694_);
v___y_2700_ = v___x_2710_;
goto v___jp_2699_;
}
else
{
lean_dec(v_fst_2694_);
v___y_2700_ = v_x_2494_;
goto v___jp_2699_;
}
v___jp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___y_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___y_2700_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_snd_2695_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2702_);
v___x_2704_ = v___x_2692_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_2494_);
return v___x_2689_;
}
}
default: 
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v_f_2493_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_x_2494_);
lean_ctor_set(v___x_2713_, 1, v___y_2495_);
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2715_, lean_object* v_x_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2715_, v_x_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2724_, lean_object* v_init_2725_, lean_object* v_e_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2724_, v_e_2726_, v_init_2725_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2741_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_snd_2737_; lean_object* v___x_2739_; 
v_snd_2737_ = lean_ctor_get(v_a_2733_, 1);
lean_inc(v_snd_2737_);
lean_dec(v_a_2733_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_snd_2737_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_snd_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_a_2742_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2732_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2732_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2750_, lean_object* v_init_2751_, lean_object* v_e_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2750_, v_init_2751_, v_e_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2761_, lean_object* v_as_2762_, size_t v_i_2763_, size_t v_stop_2764_, lean_object* v_b_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_a_2772_; uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_eq(v_i_2763_, v_stop_2764_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_array_uget_borrowed(v_as_2762_, v_i_2763_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
lean_inc(v___x_2777_);
v___x_2778_ = lean_infer_type(v___x_2777_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
lean_inc_ref(v_op_2761_);
v___x_2780_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2761_, v_a_2779_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = l_Array_append___redArg(v_b_2765_, v_a_2781_);
lean_dec(v_a_2781_);
v_a_2772_ = v___x_2782_;
goto v___jp_2771_;
}
else
{
lean_dec_ref(v_b_2765_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2783_; 
v_a_2783_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2780_);
v_a_2772_ = v_a_2783_;
goto v___jp_2771_;
}
else
{
lean_dec_ref(v_op_2761_);
return v___x_2780_;
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v_b_2765_);
lean_dec_ref(v_op_2761_);
v_a_2784_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2778_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2778_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v___x_2792_; 
lean_dec_ref(v_op_2761_);
v___x_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_b_2765_);
return v___x_2792_;
}
v___jp_2771_:
{
size_t v___x_2773_; size_t v___x_2774_; 
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2763_, v___x_2773_);
v_i_2763_ = v___x_2774_;
v_b_2765_ = v_a_2772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2793_, lean_object* v_args_2794_, lean_object* v_body_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
lean_inc_ref(v_op_2793_);
v___x_2801_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2793_, v_body_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2823_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2823_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2823_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2806_ = l_Array_reverse___redArg(v_a_2802_);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_array_get_size(v_args_2794_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref(v_op_2793_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2806_);
v___x_2811_ = v___x_2804_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_nat_dec_le(v___x_2808_, v___x_2808_);
if (v___x_2813_ == 0)
{
if (v___x_2809_ == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref(v_op_2793_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2806_);
v___x_2815_ = v___x_2804_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2806_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
else
{
size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2804_);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = lean_usize_of_nat(v___x_2808_);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2793_, v_args_2794_, v___x_2817_, v___x_2818_, v___x_2806_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2819_;
}
}
else
{
size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
lean_del_object(v___x_2804_);
v___x_2820_ = ((size_t)0ULL);
v___x_2821_ = lean_usize_of_nat(v___x_2808_);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2793_, v_args_2794_, v___x_2820_, v___x_2821_, v___x_2806_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2822_;
}
}
}
}
else
{
lean_dec_ref(v_op_2793_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2824_, lean_object* v_args_2825_, lean_object* v_body_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2824_, v_args_2825_, v_body_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec_ref(v_args_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2833_, lean_object* v_a_2834_, lean_object* v_f_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2833_, v_a_2834_, v_f_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2842_, lean_object* v_e_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
switch(lean_obj_tag(v_e_2843_))
{
case 0:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_op_2842_);
v___x_2849_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
case 7:
{
lean_object* v___f_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; 
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2851_, 0, v_op_2842_);
v___x_2852_ = 0;
v___x_2853_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2843_, v___f_2851_, v___x_2852_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2853_;
}
case 6:
{
lean_object* v___f_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; 
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2854_, 0, v_op_2842_);
v___x_2855_ = 0;
v___x_2856_ = 1;
v___x_2857_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2843_, v___f_2854_, v___x_2855_, v___x_2856_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2857_;
}
case 8:
{
lean_object* v___f_2858_; uint8_t v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; 
v___f_2858_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2858_, 0, v_op_2842_);
v___x_2859_ = 0;
v___x_2860_ = 1;
v___x_2861_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2843_, v___f_2858_, v___x_2859_, v___x_2860_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2861_;
}
default: 
{
lean_object* v___x_2862_; 
lean_inc_ref(v_op_2842_);
lean_inc(v_a_2847_);
lean_inc_ref(v_a_2846_);
lean_inc(v_a_2845_);
lean_inc_ref(v_a_2844_);
lean_inc_ref(v_e_2843_);
v___x_2862_ = lean_apply_6(v_op_2842_, v_e_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, lean_box(0));
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2864_, 0, v_op_2842_);
v___x_2865_ = l_Array_reverse___redArg(v_a_2863_);
v___x_2866_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2864_, v___x_2865_, v_e_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2866_;
}
else
{
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_op_2842_);
return v___x_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2867_, lean_object* v_a_2868_, lean_object* v_f_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2867_, v_f_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2884_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = l_Array_append___redArg(v_a_2868_, v_a_2876_);
lean_dec(v_a_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2880_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
lean_dec_ref(v_a_2868_);
return v___x_2875_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2906_, lean_object* v_op_2907_, lean_object* v_e_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2907_, v_e_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2915_, lean_object* v_op_2916_, lean_object* v_e_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2915_, v_op_2916_, v_e_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2924_, lean_object* v_op_2925_, lean_object* v_as_2926_, size_t v_i_2927_, size_t v_stop_2928_, lean_object* v_b_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2925_, v_as_2926_, v_i_2927_, v_stop_2928_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2936_, lean_object* v_op_2937_, lean_object* v_as_2938_, lean_object* v_i_2939_, lean_object* v_stop_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_i_boxed_2947_; size_t v_stop_boxed_2948_; lean_object* v_res_2949_; 
v_i_boxed_2947_ = lean_unbox_usize(v_i_2939_);
lean_dec(v_i_2939_);
v_stop_boxed_2948_ = lean_unbox_usize(v_stop_2940_);
lean_dec(v_stop_2940_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2936_, v_op_2937_, v_as_2938_, v_i_boxed_2947_, v_stop_boxed_2948_, v_b_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v_as_2938_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2950_, lean_object* v_f_2951_, lean_object* v_x_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2951_, v_x_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_f_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2960_, v_f_2961_, v_x_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2970_, lean_object* v_f_2971_, lean_object* v_init_2972_, lean_object* v_e_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2971_, v_init_2972_, v_e_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_f_2981_, lean_object* v_init_2982_, lean_object* v_e_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2980_, v_f_2981_, v_init_2982_, v_e_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2990_, size_t v_i_2991_, lean_object* v_bs_2992_){
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
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_3011_, lean_object* v_i_3012_, lean_object* v_bs_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3011_);
lean_dec(v_sz_3011_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_3014_, v_i_boxed_3015_, v_bs_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3017_, lean_object* v_j_3018_){
_start:
{
lean_object* v_zero_3019_; uint8_t v_isZero_3020_; 
v_zero_3019_ = lean_unsigned_to_nat(0u);
v_isZero_3020_ = lean_nat_dec_eq(v_j_3018_, v_zero_3019_);
if (v_isZero_3020_ == 1)
{
lean_dec(v_j_3018_);
return v_xs_3017_;
}
else
{
lean_object* v___x_3021_; lean_object* v_snd_3022_; lean_object* v_snd_3023_; lean_object* v_one_3024_; lean_object* v_n_3025_; lean_object* v___x_3026_; lean_object* v_snd_3027_; lean_object* v_snd_3028_; uint8_t v___x_3029_; 
v___x_3021_ = lean_array_fget_borrowed(v_xs_3017_, v_j_3018_);
v_snd_3022_ = lean_ctor_get(v___x_3021_, 1);
v_snd_3023_ = lean_ctor_get(v_snd_3022_, 1);
v_one_3024_ = lean_unsigned_to_nat(1u);
v_n_3025_ = lean_nat_sub(v_j_3018_, v_one_3024_);
v___x_3026_ = lean_array_fget_borrowed(v_xs_3017_, v_n_3025_);
v_snd_3027_ = lean_ctor_get(v___x_3026_, 1);
v_snd_3028_ = lean_ctor_get(v_snd_3027_, 1);
v___x_3029_ = lean_nat_dec_lt(v_snd_3028_, v_snd_3023_);
if (v___x_3029_ == 0)
{
lean_dec(v_n_3025_);
lean_dec(v_j_3018_);
return v_xs_3017_;
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_array_fswap(v_xs_3017_, v_j_3018_, v_n_3025_);
lean_dec(v_j_3018_);
v_xs_3017_ = v___x_3030_;
v_j_3018_ = v_n_3025_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3032_, lean_object* v_i_3033_, lean_object* v_fuel_3034_){
_start:
{
lean_object* v_zero_3035_; uint8_t v_isZero_3036_; 
v_zero_3035_ = lean_unsigned_to_nat(0u);
v_isZero_3036_ = lean_nat_dec_eq(v_fuel_3034_, v_zero_3035_);
if (v_isZero_3036_ == 1)
{
lean_dec(v_fuel_3034_);
lean_dec(v_i_3033_);
return v_xs_3032_;
}
else
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_array_get_size(v_xs_3032_);
v___x_3038_ = lean_nat_dec_lt(v_i_3033_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_dec(v_fuel_3034_);
lean_dec(v_i_3033_);
return v_xs_3032_;
}
else
{
lean_object* v_one_3039_; lean_object* v_n_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_one_3039_ = lean_unsigned_to_nat(1u);
v_n_3040_ = lean_nat_sub(v_fuel_3034_, v_one_3039_);
lean_dec(v_fuel_3034_);
lean_inc(v_i_3033_);
v___x_3041_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3032_, v_i_3033_);
v___x_3042_ = lean_nat_add(v_i_3033_, v_one_3039_);
lean_dec(v_i_3033_);
v_xs_3032_ = v___x_3041_;
v_i_3033_ = v___x_3042_;
v_fuel_3034_ = v_n_3040_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3044_, size_t v_i_3045_, lean_object* v_bs_3046_){
_start:
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_usize_dec_lt(v_i_3045_, v_sz_3044_);
if (v___x_3047_ == 0)
{
return v_bs_3046_;
}
else
{
lean_object* v_v_3048_; lean_object* v_fst_3049_; lean_object* v_snd_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3064_; 
v_v_3048_ = lean_array_uget(v_bs_3046_, v_i_3045_);
v_fst_3049_ = lean_ctor_get(v_v_3048_, 0);
v_snd_3050_ = lean_ctor_get(v_v_3048_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_v_3048_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3052_ = v_v_3048_;
v_isShared_3053_ = v_isSharedCheck_3064_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_snd_3050_);
lean_inc(v_fst_3049_);
lean_dec(v_v_3048_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3064_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v_bs_x27_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v_bs_x27_3055_ = lean_array_uset(v_bs_3046_, v_i_3045_, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_fst_3049_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3056_);
v___x_3058_ = v___x_3052_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_snd_3050_);
v___x_3058_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
size_t v___x_3059_; size_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = ((size_t)1ULL);
v___x_3060_ = lean_usize_add(v_i_3045_, v___x_3059_);
v___x_3061_ = lean_array_uset(v_bs_x27_3055_, v_i_3045_, v___x_3058_);
v_i_3045_ = v___x_3060_;
v_bs_3046_ = v___x_3061_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3065_, lean_object* v_i_3066_, lean_object* v_bs_3067_){
_start:
{
size_t v_sz_boxed_3068_; size_t v_i_boxed_3069_; lean_object* v_res_3070_; 
v_sz_boxed_3068_ = lean_unbox_usize(v_sz_3065_);
lean_dec(v_sz_3065_);
v_i_boxed_3069_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_res_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3068_, v_i_boxed_3069_, v_bs_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3071_, lean_object* v_as_3072_, size_t v_sz_3073_, size_t v_i_3074_, lean_object* v_b_3075_){
_start:
{
lean_object* v_a_3078_; uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_lt(v_i_3074_, v_sz_3073_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v_b_3075_);
return v___x_3083_;
}
else
{
lean_object* v_a_3084_; lean_object* v_snd_3085_; lean_object* v_snd_3086_; lean_object* v_fst_3087_; lean_object* v_fst_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3138_; 
v_a_3084_ = lean_array_uget(v_as_3072_, v_i_3074_);
v_snd_3085_ = lean_ctor_get(v_a_3084_, 1);
lean_inc(v_snd_3085_);
v_snd_3086_ = lean_ctor_get(v_b_3075_, 1);
lean_inc(v_snd_3086_);
v_fst_3087_ = lean_ctor_get(v_a_3084_, 0);
v_fst_3088_ = lean_ctor_get(v_snd_3085_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_snd_3085_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v_snd_3085_, 1);
lean_dec(v_unused_3139_);
v___x_3090_ = v_snd_3085_;
v_isShared_3091_ = v_isSharedCheck_3138_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_fst_3088_);
lean_dec(v_snd_3085_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3138_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_fst_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3136_; 
v_fst_3092_ = lean_ctor_get(v_b_3075_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_b_3075_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v_b_3075_, 1);
lean_dec(v_unused_3137_);
v___x_3094_ = v_b_3075_;
v_isShared_3095_ = v_isSharedCheck_3136_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_fst_3092_);
lean_dec(v_b_3075_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3136_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_fst_3096_; lean_object* v_snd_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3135_; 
v_fst_3096_ = lean_ctor_get(v_snd_3086_, 0);
v_snd_3097_ = lean_ctor_get(v_snd_3086_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_snd_3086_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3099_ = v_snd_3086_;
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_snd_3097_);
lean_inc(v_fst_3096_);
lean_dec(v_snd_3086_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
uint8_t v___x_3113_; 
v___x_3113_ = l_Lean_NameSet_contains(v_forbidden_3071_, v_fst_3087_);
if (v___x_3113_ == 0)
{
uint8_t v___x_3114_; 
lean_inc(v_fst_3087_);
v___x_3114_ = lean_unbox(v_fst_3088_);
lean_dec(v_fst_3088_);
if (v___x_3114_ == 0)
{
uint8_t v___x_3115_; 
lean_del_object(v___x_3099_);
lean_del_object(v___x_3094_);
v___x_3115_ = l_Lean_NameSet_contains(v_fst_3092_, v_fst_3087_);
if (v___x_3115_ == 0)
{
if (v___x_3082_ == 0)
{
lean_dec(v_fst_3087_);
lean_dec(v_a_3084_);
goto v___jp_3108_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_del_object(v___x_3090_);
v___x_3116_ = lean_array_push(v_snd_3097_, v_a_3084_);
v___x_3117_ = l_Lean_NameSet_insert(v_fst_3092_, v_fst_3087_);
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_fst_3096_);
lean_ctor_set(v___x_3118_, 1, v___x_3116_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v_a_3078_ = v___x_3119_;
goto v___jp_3077_;
}
}
else
{
lean_dec(v_fst_3087_);
lean_dec(v_a_3084_);
goto v___jp_3108_;
}
}
else
{
uint8_t v___x_3120_; 
lean_del_object(v___x_3090_);
v___x_3120_ = l_Lean_NameSet_contains(v_fst_3096_, v_fst_3087_);
if (v___x_3120_ == 0)
{
if (v___x_3082_ == 0)
{
lean_dec(v_fst_3087_);
lean_dec(v_a_3084_);
goto v___jp_3101_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_del_object(v___x_3099_);
lean_del_object(v___x_3094_);
v___x_3121_ = lean_array_push(v_snd_3097_, v_a_3084_);
v___x_3122_ = l_Lean_NameSet_insert(v_fst_3096_, v_fst_3087_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___x_3121_);
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_fst_3092_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v_a_3078_ = v___x_3124_;
goto v___jp_3077_;
}
}
else
{
lean_dec(v_fst_3087_);
lean_dec(v_a_3084_);
goto v___jp_3101_;
}
}
}
else
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
lean_del_object(v___x_3099_);
lean_del_object(v___x_3094_);
lean_del_object(v___x_3090_);
lean_dec(v_fst_3088_);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_a_3084_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3133_ = lean_ctor_get(v_a_3084_, 1);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_a_3084_, 0);
lean_dec(v_unused_3134_);
v___x_3126_ = v_a_3084_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_a_3084_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v_snd_3097_);
lean_ctor_set(v___x_3126_, 0, v_fst_3096_);
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_fst_3096_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_snd_3097_);
v___x_3129_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_fst_3092_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v_a_3078_ = v___x_3130_;
goto v___jp_3077_;
}
}
}
v___jp_3101_:
{
lean_object* v___x_3103_; 
if (v_isShared_3100_ == 0)
{
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_fst_3096_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_snd_3097_);
v___x_3103_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3105_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v___x_3103_);
v___x_3105_ = v___x_3094_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_fst_3092_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
v_a_3078_ = v___x_3105_;
goto v___jp_3077_;
}
}
}
v___jp_3108_:
{
lean_object* v___x_3110_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 1, v_snd_3097_);
lean_ctor_set(v___x_3090_, 0, v_fst_3096_);
v___x_3110_ = v___x_3090_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_fst_3096_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_snd_3097_);
v___x_3110_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_fst_3092_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v_a_3078_ = v___x_3111_;
goto v___jp_3077_;
}
}
}
}
}
}
v___jp_3077_:
{
size_t v___x_3079_; size_t v___x_3080_; 
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_add(v_i_3074_, v___x_3079_);
v_i_3074_ = v___x_3080_;
v_b_3075_ = v_a_3078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3140_, lean_object* v_as_3141_, lean_object* v_sz_3142_, lean_object* v_i_3143_, lean_object* v_b_3144_, lean_object* v___y_3145_){
_start:
{
size_t v_sz_boxed_3146_; size_t v_i_boxed_3147_; lean_object* v_res_3148_; 
v_sz_boxed_3146_ = lean_unbox_usize(v_sz_3142_);
lean_dec(v_sz_3142_);
v_i_boxed_3147_ = lean_unbox_usize(v_i_3143_);
lean_dec(v_i_3143_);
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3140_, v_as_3141_, v_sz_boxed_3146_, v_i_boxed_3147_, v_b_3144_);
lean_dec_ref(v_as_3141_);
lean_dec(v_forbidden_3140_);
return v_res_3148_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3153_ = l_Lean_MessageData_ofFormat(v___x_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_box(1);
v___x_3155_ = l_Lean_MessageData_ofFormat(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
if (lean_obj_tag(v_a_3158_) == 0)
{
lean_object* v___x_3160_; 
v___x_3160_ = l_List_reverse___redArg(v_a_3159_);
return v___x_3160_;
}
else
{
lean_object* v_head_3161_; lean_object* v_snd_3162_; lean_object* v_tail_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3208_; 
v_head_3161_ = lean_ctor_get(v_a_3158_, 0);
lean_inc(v_head_3161_);
v_snd_3162_ = lean_ctor_get(v_head_3161_, 1);
lean_inc(v_snd_3162_);
v_tail_3163_ = lean_ctor_get(v_a_3158_, 1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_3158_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_a_3158_, 0);
lean_dec(v_unused_3209_);
v___x_3165_ = v_a_3158_;
v_isShared_3166_ = v_isSharedCheck_3208_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_tail_3163_);
lean_dec(v_a_3158_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3208_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v_fst_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3206_; 
v_fst_3167_ = lean_ctor_get(v_head_3161_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_head_3161_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v_head_3161_, 1);
lean_dec(v_unused_3207_);
v___x_3169_ = v_head_3161_;
v_isShared_3170_ = v_isSharedCheck_3206_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_fst_3167_);
lean_dec(v_head_3161_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3206_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_fst_3171_; lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3205_; 
v_fst_3171_ = lean_ctor_get(v_snd_3162_, 0);
v_snd_3172_ = lean_ctor_get(v_snd_3162_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_snd_3162_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3174_ = v_snd_3162_;
v_isShared_3175_ = v_isSharedCheck_3205_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_inc(v_fst_3171_);
lean_dec(v_snd_3162_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3205_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = l_Lean_MessageData_ofName(v_fst_3167_);
v___x_3177_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 7);
lean_ctor_set(v___x_3174_, 1, v___x_3177_);
lean_ctor_set(v___x_3174_, 0, v___x_3176_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 7);
lean_ctor_set(v___x_3169_, 1, v___x_3180_);
lean_ctor_set(v___x_3169_, 0, v___x_3179_);
v___x_3182_ = v___x_3169_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___y_3184_; uint8_t v___x_3200_; 
v___x_3200_ = lean_unbox(v_fst_3171_);
lean_dec(v_fst_3171_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
v___x_3201_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3184_ = v___x_3201_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3202_; 
v___x_3202_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3184_ = v___x_3202_;
goto v___jp_3183_;
}
v___jp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_inc_ref(v___y_3184_);
v___x_3185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___y_3184_);
v___x_3186_ = l_Lean_MessageData_ofFormat(v___x_3185_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3177_);
v___x_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v___x_3180_);
v___x_3189_ = l_Nat_reprFast(v_snd_3172_);
v___x_3190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
v___x_3191_ = l_Lean_MessageData_ofFormat(v___x_3190_);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3188_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Lean_MessageData_paren(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3182_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_MessageData_paren(v___x_3194_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v_a_3159_);
lean_ctor_set(v___x_3165_, 0, v___x_3195_);
v___x_3197_ = v___x_3165_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_a_3159_);
v___x_3197_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
v_a_3158_ = v_tail_3163_;
v_a_3159_ = v___x_3197_;
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
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3213_ = l_Lean_NameSet_empty;
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3216_ = l_Lean_NameSet_empty;
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___x_3215_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3219_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3220_ = l_Lean_Name_append(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3224_, lean_object* v_moduleRef_3225_, lean_object* v_target_3226_, lean_object* v_forbidden_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3233_, 0, v_moduleRef_3225_);
v___x_3234_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3233_, v_target_3226_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; size_t v_sz_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = lean_unsigned_to_nat(0u);
v___x_3237_ = lean_array_get_size(v_a_3235_);
v___x_3238_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3235_, v___x_3236_, v___x_3237_);
v___x_3239_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3240_ = lean_array_size(v___x_3238_);
v___x_3241_ = ((size_t)0ULL);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3227_, v___x_3238_, v_sz_3240_, v___x_3241_, v___x_3239_);
lean_dec_ref(v___x_3238_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3286_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3286_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3286_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_snd_3247_; lean_object* v_snd_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3284_; 
v_snd_3247_ = lean_ctor_get(v_a_3243_, 1);
lean_inc(v_snd_3247_);
lean_dec(v_a_3243_);
v_snd_3248_ = lean_ctor_get(v_snd_3247_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_snd_3247_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; 
v_unused_3285_ = lean_ctor_get(v_snd_3247_, 0);
lean_dec(v_unused_3285_);
v___x_3250_ = v_snd_3247_;
v_isShared_3251_ = v_isSharedCheck_3284_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snd_3248_);
lean_dec(v_snd_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3284_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
v_options_3261_ = lean_ctor_get(v_a_3230_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
lean_del_object(v___x_3250_);
goto v___jp_3252_;
}
else
{
lean_object* v_inheritedTraceOptions_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_inheritedTraceOptions_3263_ = lean_ctor_get(v_a_3230_, 13);
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3265_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3263_, v_options_3261_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_del_object(v___x_3250_);
goto v___jp_3252_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3267_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3248_);
v___x_3268_ = lean_array_to_list(v_snd_3248_);
v___x_3269_ = lean_box(0);
v___x_3270_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3268_, v___x_3269_);
v___x_3271_ = l_Lean_MessageData_ofList(v___x_3270_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set_tag(v___x_3250_, 7);
lean_ctor_set(v___x_3250_, 1, v___x_3271_);
lean_ctor_set(v___x_3250_, 0, v___x_3267_);
v___x_3273_ = v___x_3250_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3264_, v___x_3273_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref(v___x_3274_);
goto v___jp_3252_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_snd_3248_);
lean_del_object(v___x_3245_);
lean_dec_ref(v_hyps_3224_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
}
v___jp_3252_:
{
size_t v_sz_3253_; lean_object* v___x_3254_; size_t v_sz_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v_sz_3253_ = lean_array_size(v_hyps_3224_);
v___x_3254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3253_, v___x_3241_, v_hyps_3224_);
v_sz_3255_ = lean_array_size(v_snd_3248_);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3255_, v___x_3241_, v_snd_3248_);
v___x_3257_ = l_Array_append___redArg(v___x_3254_, v___x_3256_);
lean_dec_ref(v___x_3256_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3257_);
v___x_3259_ = v___x_3245_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v_hyps_3224_);
v_a_3287_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3242_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3242_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v_hyps_3224_);
v_a_3295_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3234_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3234_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3303_, lean_object* v_moduleRef_3304_, lean_object* v_target_3305_, lean_object* v_forbidden_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3303_, v_moduleRef_3304_, v_target_3305_, v_forbidden_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_forbidden_3306_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3313_, lean_object* v_as_3314_, size_t v_sz_3315_, size_t v_i_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3313_, v_as_3314_, v_sz_3315_, v_i_3316_, v_b_3317_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3324_, lean_object* v_as_3325_, lean_object* v_sz_3326_, lean_object* v_i_3327_, lean_object* v_b_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
size_t v_sz_boxed_3334_; size_t v_i_boxed_3335_; lean_object* v_res_3336_; 
v_sz_boxed_3334_ = lean_unbox_usize(v_sz_3326_);
lean_dec(v_sz_3326_);
v_i_boxed_3335_ = lean_unbox_usize(v_i_3327_);
lean_dec(v_i_3327_);
v_res_3336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3324_, v_as_3325_, v_sz_boxed_3334_, v_i_boxed_3335_, v_b_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_as_3325_);
lean_dec(v_forbidden_3324_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3337_, lean_object* v_j_3338_, lean_object* v_h_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3337_, v_j_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3341_){
_start:
{
uint8_t v_rfl_x3f_3342_; 
v_rfl_x3f_3342_ = lean_ctor_get_uint8(v_r_3341_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3342_ == 0)
{
lean_object* v_result_3343_; lean_object* v_eNew_3344_; lean_object* v___x_3345_; 
v_result_3343_ = lean_ctor_get(v_r_3341_, 2);
v_eNew_3344_ = lean_ctor_get(v_result_3343_, 0);
lean_inc_ref(v_eNew_3344_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_eNew_3344_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_box(0);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3347_);
lean_dec_ref(v_r_3347_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; 
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
lean_inc(v___y_3351_);
lean_inc_ref(v___y_3350_);
v___x_3359_ = lean_apply_9(v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, lean_box(0));
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___f_3382_; lean_object* v___x_3383_; 
lean_inc(v___y_3376_);
lean_inc_ref(v___y_3375_);
lean_inc(v___y_3374_);
lean_inc_ref(v___y_3373_);
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3382_, 0, v_x_3372_);
lean_closure_set(v___f_3382_, 1, v___y_3373_);
lean_closure_set(v___f_3382_, 2, v___y_3374_);
lean_closure_set(v___f_3382_, 3, v___y_3375_);
lean_closure_set(v___f_3382_, 4, v___y_3376_);
v___x_3383_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3371_, v___f_3382_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3383_) == 0)
{
return v___x_3383_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3392_, v_x_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3404_, lean_object* v_mctx_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3405_, v_x_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3417_, lean_object* v_mctx_3418_, lean_object* v_x_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3417_, v_mctx_3418_, v_x_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3430_, uint8_t v_symm_3431_, lean_object* v_r_3432_, lean_object* v_ref_3433_, lean_object* v_checkState_x3f_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3436_, v___y_3438_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v_ref_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___y_3456_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v_ref_3446_ = lean_ctor_get(v___y_3441_, 5);
v___x_3447_ = lean_box(v_symm_3431_);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_expr_3430_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = lean_box(0);
v___x_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3432_);
v___x_3452_ = l_Option_toLOption___redArg(v___x_3451_);
v___x_3453_ = lean_box(0);
lean_inc(v_ref_3446_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_ref_3446_);
if (lean_obj_tag(v_checkState_x3f_3434_) == 0)
{
v___y_3456_ = v_a_3445_;
goto v___jp_3455_;
}
else
{
lean_object* v_val_3459_; 
lean_dec(v_a_3445_);
v_val_3459_ = lean_ctor_get(v_checkState_x3f_3434_, 0);
lean_inc(v_val_3459_);
lean_dec_ref(v_checkState_x3f_3434_);
v___y_3456_ = v_val_3459_;
goto v___jp_3455_;
}
v___jp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___y_3456_);
v___x_3458_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3433_, v___x_3450_, v___x_3452_, v___x_3453_, v___x_3454_, v___x_3457_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3458_;
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_checkState_x3f_3434_);
lean_dec(v_ref_3433_);
lean_dec_ref(v_expr_3430_);
v_a_3460_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3444_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3444_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3468_, lean_object* v_symm_3469_, lean_object* v_r_3470_, lean_object* v_ref_3471_, lean_object* v_checkState_x3f_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
uint8_t v_symm_boxed_3482_; lean_object* v_res_3483_; 
v_symm_boxed_3482_ = lean_unbox(v_symm_3469_);
v_res_3483_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3468_, v_symm_boxed_3482_, v_r_3470_, v_ref_3471_, v_checkState_x3f_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec_ref(v_r_3470_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3484_, lean_object* v_r_3485_, lean_object* v_checkState_x3f_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_expr_3496_; uint8_t v_symm_3497_; lean_object* v_mctx_3498_; lean_object* v___x_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; 
v_expr_3496_ = lean_ctor_get(v_r_3485_, 0);
lean_inc_ref(v_expr_3496_);
v_symm_3497_ = lean_ctor_get_uint8(v_r_3485_, sizeof(void*)*4);
v_mctx_3498_ = lean_ctor_get(v_r_3485_, 3);
lean_inc_ref(v_mctx_3498_);
v___x_3499_ = lean_box(v_symm_3497_);
v___f_3500_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3500_, 0, v_expr_3496_);
lean_closure_set(v___f_3500_, 1, v___x_3499_);
lean_closure_set(v___f_3500_, 2, v_r_3485_);
lean_closure_set(v___f_3500_, 3, v_ref_3484_);
lean_closure_set(v___f_3500_, 4, v_checkState_x3f_3486_);
v___x_3501_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3498_, v___f_3500_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3502_, lean_object* v_r_3503_, lean_object* v_checkState_x3f_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3502_, v_r_3503_, v_checkState_x3f_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3515_, lean_object* v_b_3516_, lean_object* v_x_3517_){
_start:
{
if (lean_obj_tag(v_x_3517_) == 0)
{
lean_dec(v_b_3516_);
lean_dec_ref(v_a_3515_);
return v_x_3517_;
}
else
{
lean_object* v_key_3518_; lean_object* v_value_3519_; lean_object* v_tail_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3532_; 
v_key_3518_ = lean_ctor_get(v_x_3517_, 0);
v_value_3519_ = lean_ctor_get(v_x_3517_, 1);
v_tail_3520_ = lean_ctor_get(v_x_3517_, 2);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_x_3517_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3522_ = v_x_3517_;
v_isShared_3523_ = v_isSharedCheck_3532_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_tail_3520_);
lean_inc(v_value_3519_);
lean_inc(v_key_3518_);
lean_dec(v_x_3517_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3532_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_string_dec_eq(v_key_3518_, v_a_3515_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3515_, v_b_3516_, v_tail_3520_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 2, v___x_3525_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_key_3518_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_value_3519_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
else
{
lean_object* v___x_3530_; 
lean_dec(v_value_3519_);
lean_dec(v_key_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 1, v_b_3516_);
lean_ctor_set(v___x_3522_, 0, v_a_3515_);
v___x_3530_ = v___x_3522_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3515_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_b_3516_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_tail_3520_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
if (lean_obj_tag(v_x_3534_) == 0)
{
return v_x_3533_;
}
else
{
lean_object* v_key_3535_; lean_object* v_value_3536_; lean_object* v_tail_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3560_; 
v_key_3535_ = lean_ctor_get(v_x_3534_, 0);
v_value_3536_ = lean_ctor_get(v_x_3534_, 1);
v_tail_3537_ = lean_ctor_get(v_x_3534_, 2);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_x_3534_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3539_ = v_x_3534_;
v_isShared_3540_ = v_isSharedCheck_3560_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_tail_3537_);
lean_inc(v_value_3536_);
lean_inc(v_key_3535_);
lean_dec(v_x_3534_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3560_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; uint64_t v___x_3542_; uint64_t v___x_3543_; uint64_t v___x_3544_; uint64_t v_fold_3545_; uint64_t v___x_3546_; uint64_t v___x_3547_; uint64_t v___x_3548_; size_t v___x_3549_; size_t v___x_3550_; size_t v___x_3551_; size_t v___x_3552_; size_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3541_ = lean_array_get_size(v_x_3533_);
v___x_3542_ = lean_string_hash(v_key_3535_);
v___x_3543_ = 32ULL;
v___x_3544_ = lean_uint64_shift_right(v___x_3542_, v___x_3543_);
v_fold_3545_ = lean_uint64_xor(v___x_3542_, v___x_3544_);
v___x_3546_ = 16ULL;
v___x_3547_ = lean_uint64_shift_right(v_fold_3545_, v___x_3546_);
v___x_3548_ = lean_uint64_xor(v_fold_3545_, v___x_3547_);
v___x_3549_ = lean_uint64_to_usize(v___x_3548_);
v___x_3550_ = lean_usize_of_nat(v___x_3541_);
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_sub(v___x_3550_, v___x_3551_);
v___x_3553_ = lean_usize_land(v___x_3549_, v___x_3552_);
v___x_3554_ = lean_array_uget_borrowed(v_x_3533_, v___x_3553_);
lean_inc(v___x_3554_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 2, v___x_3554_);
v___x_3556_ = v___x_3539_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_key_3535_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_value_3536_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_array_uset(v_x_3533_, v___x_3553_, v___x_3556_);
v_x_3533_ = v___x_3557_;
v_x_3534_ = v_tail_3537_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3561_, lean_object* v_source_3562_, lean_object* v_target_3563_){
_start:
{
lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = lean_array_get_size(v_source_3562_);
v___x_3565_ = lean_nat_dec_lt(v_i_3561_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_dec_ref(v_source_3562_);
lean_dec(v_i_3561_);
return v_target_3563_;
}
else
{
lean_object* v_es_3566_; lean_object* v___x_3567_; lean_object* v_source_3568_; lean_object* v_target_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_es_3566_ = lean_array_fget(v_source_3562_, v_i_3561_);
v___x_3567_ = lean_box(0);
v_source_3568_ = lean_array_fset(v_source_3562_, v_i_3561_, v___x_3567_);
v_target_3569_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3563_, v_es_3566_);
v___x_3570_ = lean_unsigned_to_nat(1u);
v___x_3571_ = lean_nat_add(v_i_3561_, v___x_3570_);
lean_dec(v_i_3561_);
v_i_3561_ = v___x_3571_;
v_source_3562_ = v_source_3568_;
v_target_3563_ = v_target_3569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v_nbuckets_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3574_ = lean_array_get_size(v_data_3573_);
v___x_3575_ = lean_unsigned_to_nat(2u);
v_nbuckets_3576_ = lean_nat_mul(v___x_3574_, v___x_3575_);
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = lean_box(0);
v___x_3579_ = lean_mk_array(v_nbuckets_3576_, v___x_3578_);
v___x_3580_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3577_, v_data_3573_, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3581_, lean_object* v_x_3582_){
_start:
{
if (lean_obj_tag(v_x_3582_) == 0)
{
uint8_t v___x_3583_; 
v___x_3583_ = 0;
return v___x_3583_;
}
else
{
lean_object* v_key_3584_; lean_object* v_tail_3585_; uint8_t v___x_3586_; 
v_key_3584_ = lean_ctor_get(v_x_3582_, 0);
v_tail_3585_ = lean_ctor_get(v_x_3582_, 2);
v___x_3586_ = lean_string_dec_eq(v_key_3584_, v_a_3581_);
if (v___x_3586_ == 0)
{
v_x_3582_ = v_tail_3585_;
goto _start;
}
else
{
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3588_, lean_object* v_x_3589_){
_start:
{
uint8_t v_res_3590_; lean_object* v_r_3591_; 
v_res_3590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3588_, v_x_3589_);
lean_dec(v_x_3589_);
lean_dec_ref(v_a_3588_);
v_r_3591_ = lean_box(v_res_3590_);
return v_r_3591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3592_, lean_object* v_a_3593_, lean_object* v_b_3594_){
_start:
{
lean_object* v_size_3595_; lean_object* v_buckets_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3639_; 
v_size_3595_ = lean_ctor_get(v_m_3592_, 0);
v_buckets_3596_ = lean_ctor_get(v_m_3592_, 1);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_m_3592_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3598_ = v_m_3592_;
v_isShared_3599_ = v_isSharedCheck_3639_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_buckets_3596_);
lean_inc(v_size_3595_);
lean_dec(v_m_3592_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3639_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; uint64_t v___x_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v_fold_3604_; uint64_t v___x_3605_; uint64_t v___x_3606_; uint64_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; lean_object* v_bkt_3613_; uint8_t v___x_3614_; 
v___x_3600_ = lean_array_get_size(v_buckets_3596_);
v___x_3601_ = lean_string_hash(v_a_3593_);
v___x_3602_ = 32ULL;
v___x_3603_ = lean_uint64_shift_right(v___x_3601_, v___x_3602_);
v_fold_3604_ = lean_uint64_xor(v___x_3601_, v___x_3603_);
v___x_3605_ = 16ULL;
v___x_3606_ = lean_uint64_shift_right(v_fold_3604_, v___x_3605_);
v___x_3607_ = lean_uint64_xor(v_fold_3604_, v___x_3606_);
v___x_3608_ = lean_uint64_to_usize(v___x_3607_);
v___x_3609_ = lean_usize_of_nat(v___x_3600_);
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_sub(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_usize_land(v___x_3608_, v___x_3611_);
v_bkt_3613_ = lean_array_uget_borrowed(v_buckets_3596_, v___x_3612_);
v___x_3614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3593_, v_bkt_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v_size_x27_3616_; lean_object* v___x_3617_; lean_object* v_buckets_x27_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3615_ = lean_unsigned_to_nat(1u);
v_size_x27_3616_ = lean_nat_add(v_size_3595_, v___x_3615_);
lean_dec(v_size_3595_);
lean_inc(v_bkt_3613_);
v___x_3617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3617_, 0, v_a_3593_);
lean_ctor_set(v___x_3617_, 1, v_b_3594_);
lean_ctor_set(v___x_3617_, 2, v_bkt_3613_);
v_buckets_x27_3618_ = lean_array_uset(v_buckets_3596_, v___x_3612_, v___x_3617_);
v___x_3619_ = lean_unsigned_to_nat(4u);
v___x_3620_ = lean_nat_mul(v_size_x27_3616_, v___x_3619_);
v___x_3621_ = lean_unsigned_to_nat(3u);
v___x_3622_ = lean_nat_div(v___x_3620_, v___x_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_array_get_size(v_buckets_x27_3618_);
v___x_3624_ = lean_nat_dec_le(v___x_3622_, v___x_3623_);
lean_dec(v___x_3622_);
if (v___x_3624_ == 0)
{
lean_object* v_val_3625_; lean_object* v___x_3627_; 
v_val_3625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3618_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_val_3625_);
lean_ctor_set(v___x_3598_, 0, v_size_x27_3616_);
v___x_3627_ = v___x_3598_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_size_x27_3616_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_val_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
else
{
lean_object* v___x_3630_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_buckets_x27_3618_);
lean_ctor_set(v___x_3598_, 0, v_size_x27_3616_);
v___x_3630_ = v___x_3598_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_size_x27_3616_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_buckets_x27_3618_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
else
{
lean_object* v___x_3632_; lean_object* v_buckets_x27_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_inc(v_bkt_3613_);
v___x_3632_ = lean_box(0);
v_buckets_x27_3633_ = lean_array_uset(v_buckets_3596_, v___x_3612_, v___x_3632_);
v___x_3634_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3593_, v_b_3594_, v_bkt_3613_);
v___x_3635_ = lean_array_uset(v_buckets_x27_3633_, v___x_3612_, v___x_3634_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v___x_3635_);
v___x_3637_ = v___x_3598_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_size_3595_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_buckets_3642_; lean_object* v___x_3643_; uint64_t v___x_3644_; uint64_t v___x_3645_; uint64_t v___x_3646_; uint64_t v_fold_3647_; uint64_t v___x_3648_; uint64_t v___x_3649_; uint64_t v___x_3650_; size_t v___x_3651_; size_t v___x_3652_; size_t v___x_3653_; size_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_buckets_3642_ = lean_ctor_get(v_m_3640_, 1);
v___x_3643_ = lean_array_get_size(v_buckets_3642_);
v___x_3644_ = lean_string_hash(v_a_3641_);
v___x_3645_ = 32ULL;
v___x_3646_ = lean_uint64_shift_right(v___x_3644_, v___x_3645_);
v_fold_3647_ = lean_uint64_xor(v___x_3644_, v___x_3646_);
v___x_3648_ = 16ULL;
v___x_3649_ = lean_uint64_shift_right(v_fold_3647_, v___x_3648_);
v___x_3650_ = lean_uint64_xor(v_fold_3647_, v___x_3649_);
v___x_3651_ = lean_uint64_to_usize(v___x_3650_);
v___x_3652_ = lean_usize_of_nat(v___x_3643_);
v___x_3653_ = ((size_t)1ULL);
v___x_3654_ = lean_usize_sub(v___x_3652_, v___x_3653_);
v___x_3655_ = lean_usize_land(v___x_3651_, v___x_3654_);
v___x_3656_ = lean_array_uget_borrowed(v_buckets_3642_, v___x_3655_);
v___x_3657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3641_, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3658_, lean_object* v_a_3659_){
_start:
{
uint8_t v_res_3660_; lean_object* v_r_3661_; 
v_res_3660_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3658_, v_a_3659_);
lean_dec_ref(v_a_3659_);
lean_dec_ref(v_m_3658_);
v_r_3661_ = lean_box(v_res_3660_);
return v_r_3661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3662_, lean_object* v_as_x27_3663_, lean_object* v_b_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
if (lean_obj_tag(v_as_x27_3663_) == 0)
{
lean_object* v___x_3670_; 
lean_dec_ref(v_cfg_3662_);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v_b_3664_);
return v___x_3670_;
}
else
{
lean_object* v_head_3671_; lean_object* v_snd_3672_; lean_object* v_tail_3673_; lean_object* v_fst_3674_; lean_object* v_fst_3675_; lean_object* v_snd_3676_; lean_object* v___x_3677_; 
v_head_3671_ = lean_ctor_get(v_as_x27_3663_, 0);
v_snd_3672_ = lean_ctor_get(v_head_3671_, 1);
v_tail_3673_ = lean_ctor_get(v_as_x27_3663_, 1);
v_fst_3674_ = lean_ctor_get(v_head_3671_, 0);
v_fst_3675_ = lean_ctor_get(v_snd_3672_, 0);
v_snd_3676_ = lean_ctor_get(v_snd_3672_, 1);
v___x_3677_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3667_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_snd_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3822_; 
v_snd_3678_ = lean_ctor_get(v_b_3664_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_b_3664_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v_b_3664_, 0);
lean_dec(v_unused_3823_);
v___x_3680_ = v_b_3664_;
v_isShared_3681_ = v_isSharedCheck_3822_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_snd_3678_);
lean_dec(v_b_3664_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3822_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3821_; 
v_a_3682_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3684_ = v___x_3677_;
v_isShared_3685_ = v_isSharedCheck_3821_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3677_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3821_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v_fst_3686_; lean_object* v_snd_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3820_; 
v_fst_3686_ = lean_ctor_get(v_snd_3678_, 0);
v_snd_3687_ = lean_ctor_get(v_snd_3678_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_snd_3678_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3689_ = v_snd_3678_;
v_isShared_3690_ = v_isSharedCheck_3820_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_snd_3687_);
lean_inc(v_fst_3686_);
lean_dec(v_snd_3678_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3820_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
uint8_t v_stopAtRfl_3691_; lean_object* v_max_3692_; lean_object* v_minHeartbeats_3693_; lean_object* v_goal_3694_; lean_object* v_target_3695_; uint8_t v_side_3696_; lean_object* v_mctx_3697_; uint8_t v___x_3698_; 
v_stopAtRfl_3691_ = lean_ctor_get_uint8(v_cfg_3662_, sizeof(void*)*5);
v_max_3692_ = lean_ctor_get(v_cfg_3662_, 0);
v_minHeartbeats_3693_ = lean_ctor_get(v_cfg_3662_, 1);
v_goal_3694_ = lean_ctor_get(v_cfg_3662_, 2);
v_target_3695_ = lean_ctor_get(v_cfg_3662_, 3);
v_side_3696_ = lean_ctor_get_uint8(v_cfg_3662_, sizeof(void*)*5 + 1);
v_mctx_3697_ = lean_ctor_get(v_cfg_3662_, 4);
v___x_3698_ = lean_nat_dec_lt(v_a_3682_, v_minHeartbeats_3693_);
lean_dec(v_a_3682_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = lean_array_get_size(v_snd_3687_);
v___x_3700_ = lean_nat_dec_le(v_max_3692_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_del_object(v___x_3684_);
v___x_3701_ = lean_box(v_side_3696_);
lean_inc(v_snd_3676_);
lean_inc(v_fst_3675_);
lean_inc(v_fst_3674_);
lean_inc_ref(v_target_3695_);
lean_inc(v_goal_3694_);
lean_inc_ref_n(v_mctx_3697_, 2);
v___x_3702_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3702_, 0, v_mctx_3697_);
lean_closure_set(v___x_3702_, 1, v_goal_3694_);
lean_closure_set(v___x_3702_, 2, v_target_3695_);
lean_closure_set(v___x_3702_, 3, v___x_3701_);
lean_closure_set(v___x_3702_, 4, v_fst_3674_);
lean_closure_set(v___x_3702_, 5, v_fst_3675_);
lean_closure_set(v___x_3702_, 6, v_snd_3676_);
v___x_3703_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3703_, 0, lean_box(0));
lean_closure_set(v___x_3703_, 1, v_mctx_3697_);
lean_closure_set(v___x_3703_, 2, v___x_3702_);
v___x_3704_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3703_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
v___x_3706_ = lean_box(0);
if (lean_obj_tag(v_a_3705_) == 0)
{
lean_object* v___x_3708_; 
if (v_isShared_3690_ == 0)
{
v___x_3708_ = v___x_3689_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_snd_3687_);
v___x_3708_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3708_);
lean_ctor_set(v___x_3680_, 0, v___x_3706_);
v___x_3710_ = v___x_3680_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
v_as_x27_3663_ = v_tail_3673_;
v_b_3664_ = v___x_3710_;
goto _start;
}
}
}
else
{
lean_object* v_val_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3791_; 
v_val_3714_ = lean_ctor_get(v_a_3705_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3705_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3716_ = v_a_3705_;
v_isShared_3717_ = v_isSharedCheck_3791_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_val_3714_);
lean_dec(v_a_3705_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3791_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_result_3718_; lean_object* v_mctx_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_result_3718_ = lean_ctor_get(v_val_3714_, 2);
v_mctx_3719_ = lean_ctor_get(v_val_3714_, 3);
lean_inc(v_val_3714_);
v___x_3720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3720_, 0, v_val_3714_);
lean_inc_ref(v_mctx_3719_);
v___x_3721_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3721_, 0, lean_box(0));
lean_closure_set(v___x_3721_, 1, v_mctx_3719_);
lean_closure_set(v___x_3721_, 2, v___x_3720_);
v___x_3722_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3721_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; uint8_t v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3686_, v_a_3723_);
if (v___x_3724_ == 0)
{
lean_object* v_eNew_3725_; lean_object* v___x_3726_; 
v_eNew_3725_ = lean_ctor_get(v_result_3718_, 0);
lean_inc_ref(v_eNew_3725_);
lean_inc_ref(v_mctx_3719_);
v___x_3726_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3719_, v_eNew_3725_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3726_) == 0)
{
if (v_stopAtRfl_3691_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_dec_ref(v___x_3726_);
lean_del_object(v___x_3716_);
v___x_3727_ = lean_box(0);
v___x_3728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3686_, v_a_3723_, v___x_3727_);
v___x_3729_ = lean_array_push(v_snd_3687_, v_val_3714_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 1, v___x_3729_);
lean_ctor_set(v___x_3689_, 0, v___x_3728_);
v___x_3731_ = v___x_3689_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3731_);
lean_ctor_set(v___x_3680_, 0, v___x_3706_);
v___x_3733_ = v___x_3680_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
v_as_x27_3663_ = v_tail_3673_;
v_b_3664_ = v___x_3733_;
goto _start;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3767_; 
v_a_3737_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3739_ = v___x_3726_;
v_isShared_3740_ = v_isSharedCheck_3767_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3726_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3767_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
uint8_t v___x_3741_; 
v___x_3741_ = lean_unbox(v_a_3737_);
lean_dec(v_a_3737_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_del_object(v___x_3739_);
lean_del_object(v___x_3716_);
v___x_3742_ = lean_box(0);
v___x_3743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3686_, v_a_3723_, v___x_3742_);
v___x_3744_ = lean_array_push(v_snd_3687_, v_val_3714_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 1, v___x_3744_);
lean_ctor_set(v___x_3689_, 0, v___x_3743_);
v___x_3746_ = v___x_3689_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3746_);
lean_ctor_set(v___x_3680_, 0, v___x_3706_);
v___x_3748_ = v___x_3680_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
v_as_x27_3663_ = v_tail_3673_;
v_b_3664_ = v___x_3748_;
goto _start;
}
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec(v_a_3723_);
lean_dec_ref(v_cfg_3662_);
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_mk_empty_array_with_capacity(v___x_3752_);
v___x_3754_ = lean_array_push(v___x_3753_, v_val_3714_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3754_);
v___x_3756_ = v___x_3716_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3690_ == 0)
{
v___x_3758_ = v___x_3689_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_snd_3687_);
v___x_3758_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3758_);
lean_ctor_set(v___x_3680_, 0, v___x_3756_);
v___x_3760_ = v___x_3680_;
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
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3760_);
v___x_3762_ = v___x_3739_;
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
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_a_3723_);
lean_del_object(v___x_3716_);
lean_dec(v_val_3714_);
lean_del_object(v___x_3689_);
lean_dec(v_snd_3687_);
lean_dec(v_fst_3686_);
lean_del_object(v___x_3680_);
lean_dec_ref(v_cfg_3662_);
v_a_3768_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3726_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3726_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3777_; 
lean_dec(v_a_3723_);
lean_del_object(v___x_3716_);
lean_dec(v_val_3714_);
if (v_isShared_3690_ == 0)
{
v___x_3777_ = v___x_3689_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_snd_3687_);
v___x_3777_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3777_);
lean_ctor_set(v___x_3680_, 0, v___x_3706_);
v___x_3779_ = v___x_3680_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
v_as_x27_3663_ = v_tail_3673_;
v_b_3664_ = v___x_3779_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3716_);
lean_dec(v_val_3714_);
lean_del_object(v___x_3689_);
lean_dec(v_snd_3687_);
lean_dec(v_fst_3686_);
lean_del_object(v___x_3680_);
lean_dec_ref(v_cfg_3662_);
v_a_3783_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3722_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3722_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
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
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_del_object(v___x_3689_);
lean_dec(v_snd_3687_);
lean_dec(v_fst_3686_);
lean_del_object(v___x_3680_);
lean_dec_ref(v_cfg_3662_);
v_a_3792_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3704_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3704_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_dec_ref(v_cfg_3662_);
lean_inc(v_snd_3687_);
v___x_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3800_, 0, v_snd_3687_);
if (v_isShared_3690_ == 0)
{
v___x_3802_ = v___x_3689_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_snd_3687_);
v___x_3802_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3804_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3802_);
lean_ctor_set(v___x_3680_, 0, v___x_3800_);
v___x_3804_ = v___x_3680_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3800_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3806_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3804_);
v___x_3806_ = v___x_3684_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
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
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
lean_dec_ref(v_cfg_3662_);
lean_inc(v_snd_3687_);
v___x_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3810_, 0, v_snd_3687_);
if (v_isShared_3690_ == 0)
{
v___x_3812_ = v___x_3689_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_snd_3687_);
v___x_3812_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3812_);
lean_ctor_set(v___x_3680_, 0, v___x_3810_);
v___x_3814_ = v___x_3680_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3814_);
v___x_3816_ = v___x_3684_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
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
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_b_3664_);
lean_dec_ref(v_cfg_3662_);
v_a_3824_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3677_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3677_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3832_, lean_object* v_as_x27_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3832_, v_as_x27_3833_, v_b_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v_as_x27_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3841_, lean_object* v_seen_3842_, lean_object* v_acc_3843_, lean_object* v_xs_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3850_ = lean_box(0);
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v_seen_3842_);
lean_ctor_set(v___x_3851_, 1, v_acc_3843_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3850_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3841_, v_xs_3844_, v___x_3852_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3868_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3868_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3868_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v_fst_3858_; 
v_fst_3858_ = lean_ctor_get(v_a_3854_, 0);
if (lean_obj_tag(v_fst_3858_) == 0)
{
lean_object* v_snd_3859_; lean_object* v_snd_3860_; lean_object* v___x_3862_; 
v_snd_3859_ = lean_ctor_get(v_a_3854_, 1);
lean_inc(v_snd_3859_);
lean_dec(v_a_3854_);
v_snd_3860_ = lean_ctor_get(v_snd_3859_, 1);
lean_inc(v_snd_3860_);
lean_dec(v_snd_3859_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_snd_3860_);
v___x_3862_ = v___x_3856_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_snd_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
else
{
lean_object* v_val_3864_; lean_object* v___x_3866_; 
lean_inc_ref(v_fst_3858_);
lean_dec(v_a_3854_);
v_val_3864_ = lean_ctor_get(v_fst_3858_, 0);
lean_inc(v_val_3864_);
lean_dec_ref(v_fst_3858_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_val_3864_);
v___x_3866_ = v___x_3856_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_val_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
v_a_3869_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3853_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3853_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3877_, lean_object* v_seen_3878_, lean_object* v_acc_3879_, lean_object* v_xs_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3877_, v_seen_3878_, v_acc_3879_, v_xs_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_xs_3880_);
return v_res_3886_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3887_, lean_object* v_m_3888_, lean_object* v_a_3889_){
_start:
{
uint8_t v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3888_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3891_, lean_object* v_m_3892_, lean_object* v_a_3893_){
_start:
{
uint8_t v_res_3894_; lean_object* v_r_3895_; 
v_res_3894_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3891_, v_m_3892_, v_a_3893_);
lean_dec_ref(v_a_3893_);
lean_dec_ref(v_m_3892_);
v_r_3895_ = lean_box(v_res_3894_);
return v_r_3895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3896_, lean_object* v_m_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3897_, v_a_3898_, v_b_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3901_, lean_object* v_as_3902_, lean_object* v_as_x27_3903_, lean_object* v_b_3904_, lean_object* v_a_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3901_, v_as_x27_3903_, v_b_3904_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3912_, lean_object* v_as_3913_, lean_object* v_as_x27_3914_, lean_object* v_b_3915_, lean_object* v_a_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3912_, v_as_3913_, v_as_x27_3914_, v_b_3915_, v_a_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v_as_x27_3914_);
lean_dec(v_as_3913_);
return v_res_3922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3923_, lean_object* v_a_3924_, lean_object* v_x_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3924_, v_x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3927_, lean_object* v_a_3928_, lean_object* v_x_3929_){
_start:
{
uint8_t v_res_3930_; lean_object* v_r_3931_; 
v_res_3930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3927_, v_a_3928_, v_x_3929_);
lean_dec(v_x_3929_);
lean_dec_ref(v_a_3928_);
v_r_3931_ = lean_box(v_res_3930_);
return v_r_3931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3932_, lean_object* v_data_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3935_, lean_object* v_a_3936_, lean_object* v_b_3937_, lean_object* v_x_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3936_, v_b_3937_, v_x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3940_, lean_object* v_i_3941_, lean_object* v_source_3942_, lean_object* v_target_3943_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3941_, v_source_3942_, v_target_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3945_, lean_object* v_x_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3946_, v_x_3947_);
return v___x_3948_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_box(0);
v___x_3950_ = lean_unsigned_to_nat(16u);
v___x_3951_ = lean_mk_array(v___x_3950_, v___x_3949_);
return v___x_3951_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3955_, lean_object* v_moduleRef_3956_, lean_object* v_goal_3957_, lean_object* v_target_3958_, lean_object* v_forbidden_3959_, uint8_t v_side_3960_, uint8_t v_stopAtRfl_3961_, lean_object* v_max_3962_, lean_object* v_leavePercentHeartbeats_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_st_ref_get(v_a_3965_);
lean_inc_ref(v_target_3958_);
v___x_3970_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3955_, v_moduleRef_3956_, v_target_3958_, v_forbidden_3959_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
v___x_3972_ = l_Lean_getMaxHeartbeats___redArg(v_a_3966_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v_mctx_3974_; lean_object* v_minHeartbeats_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v_mctx_3974_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_mctx_3974_);
lean_dec(v___x_3969_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_nat_dec_eq(v_a_3973_, v___x_4003_);
lean_dec(v_a_3973_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3966_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
v___x_4007_ = lean_nat_mul(v_leavePercentHeartbeats_3963_, v_a_4006_);
lean_dec(v_a_4006_);
v___x_4008_ = lean_unsigned_to_nat(100u);
v___x_4009_ = lean_nat_div(v___x_4007_, v___x_4008_);
lean_dec(v___x_4007_);
v_minHeartbeats_3976_ = v___x_4009_;
v___y_3977_ = v_a_3964_;
v___y_3978_ = v_a_3965_;
v___y_3979_ = v_a_3966_;
v___y_3980_ = v_a_3967_;
goto v___jp_3975_;
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v_mctx_3974_);
lean_dec(v_a_3971_);
lean_dec(v_max_3962_);
lean_dec_ref(v_target_3958_);
lean_dec(v_goal_3957_);
v_a_4010_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4005_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4005_);
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
else
{
v_minHeartbeats_3976_ = v___x_4003_;
v___y_3977_ = v_a_3964_;
v___y_3978_ = v_a_3965_;
v___y_3979_ = v_a_3966_;
v___y_3980_ = v_a_3967_;
goto v___jp_3975_;
}
v___jp_3975_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_inc(v_max_3962_);
v___x_3981_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3981_, 0, v_max_3962_);
lean_ctor_set(v___x_3981_, 1, v_minHeartbeats_3976_);
lean_ctor_set(v___x_3981_, 2, v_goal_3957_);
lean_ctor_set(v___x_3981_, 3, v_target_3958_);
lean_ctor_set(v___x_3981_, 4, v_mctx_3974_);
lean_ctor_set_uint8(v___x_3981_, sizeof(void*)*5, v_stopAtRfl_3961_);
lean_ctor_set_uint8(v___x_3981_, sizeof(void*)*5 + 1, v_side_3960_);
v___x_3982_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3983_ = lean_mk_empty_array_with_capacity(v_max_3962_);
lean_dec(v_max_3962_);
v___x_3984_ = lean_array_to_list(v_a_3971_);
v___x_3985_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3981_, v___x_3982_, v___x_3983_, v___x_3984_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec(v___x_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3994_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_array_to_list(v_a_3986_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3990_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3985_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3985_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_a_3971_);
lean_dec(v___x_3969_);
lean_dec(v_max_3962_);
lean_dec_ref(v_target_3958_);
lean_dec(v_goal_3957_);
v_a_4018_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_3972_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_3972_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec(v___x_3969_);
lean_dec(v_max_3962_);
lean_dec_ref(v_target_3958_);
lean_dec(v_goal_3957_);
v_a_4026_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3970_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3970_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4034_, lean_object* v_moduleRef_4035_, lean_object* v_goal_4036_, lean_object* v_target_4037_, lean_object* v_forbidden_4038_, lean_object* v_side_4039_, lean_object* v_stopAtRfl_4040_, lean_object* v_max_4041_, lean_object* v_leavePercentHeartbeats_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
uint8_t v_side_boxed_4048_; uint8_t v_stopAtRfl_boxed_4049_; lean_object* v_res_4050_; 
v_side_boxed_4048_ = lean_unbox(v_side_4039_);
v_stopAtRfl_boxed_4049_ = lean_unbox(v_stopAtRfl_4040_);
v_res_4050_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4034_, v_moduleRef_4035_, v_goal_4036_, v_target_4037_, v_forbidden_4038_, v_side_boxed_4048_, v_stopAtRfl_boxed_4049_, v_max_4041_, v_leavePercentHeartbeats_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_leavePercentHeartbeats_4042_);
lean_dec(v_forbidden_4038_);
return v_res_4050_;
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

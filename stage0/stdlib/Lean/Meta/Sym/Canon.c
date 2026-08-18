// Lean compiler output
// Module: Lean.Meta.Sym.Canon
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ExprPtr import Lean.Meta.SynthInstance import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Arith.EvalNum import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters import Lean.Meta.Sym.Eta import Lean.Meta.WHNF import Init.Grind.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_Lean_Expr_isBoolTrue(lean_object*);
uint8_t l_Lean_Expr_isBoolFalse(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "canon"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 1, 190, 45, 30, 82, 81, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 97, 144, 214, 78, 119, 236, 177)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 84, 158, 71, 120, 158, 242, 63)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Canon"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 83, 125, 6, 218, 3, 48, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 171, 198, 108, 141, 151, 61, 31)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 129, 34, 172, 72, 50, 70, 116)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 207, 82, 133, 112, 147, 195, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 103, 41, 34, 191, 138, 48, 228)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 52, 130, 106, 6, 185, 228, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 111, 38, 159, 202, 81, 240, 140)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 83, 198, 225, 249, 91, 57, 132)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 226, 138, 193, 30, 68, 227, 228)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 70, 161, 93, 218, 182, 14, 120)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 112, 163, 177, 100, 91, 121, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 6, 28, 240, 79, 58, 119, 82)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1925315962) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(161, 32, 45, 47, 13, 228, 196, 13)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 31, 210, 182, 50, 29, 226, 12)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 160, 218, 47, 172, 76, 255, 193)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(63, 7, 146, 163, 93, 52, 225, 8)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonType"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonInst"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "canonImplicit"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "visit"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to canonicalize instance"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nsynthesized instance is not definitionally equal"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nfailed to synthesize"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__5(lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_canon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sym canon"};
static const lean_object* l_Lean_Meta_Sym_canon___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_canon___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_79_ = 0;
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_81_ = l_Lean_registerTraceClass(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(lean_object* v_args_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = lean_array_get_size(v_args_95_);
v___x_171_ = lean_unsigned_to_nat(3u);
v___x_172_ = lean_nat_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_args_95_);
goto v___jp_101_;
}
else
{
uint8_t v_modified_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v_modified_177_; 
v_modified_173_ = 0;
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_array_fget_borrowed(v_args_95_, v___x_174_);
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_177_ = l_Lean_Expr_isAppOf(v___x_175_, v___x_176_);
if (v_modified_177_ == 0)
{
v_args_140_ = v_args_95_;
v_modified_141_ = v_modified_173_;
v___y_142_ = v_a_97_;
goto v___jp_139_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_getNatValue_x3f(v___x_175_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_val_180_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v_a_179_, 1);
v___x_181_ = l_Lean_mkRawNatLit(v_val_180_);
v___x_182_ = lean_array_fset(v_args_95_, v___x_174_, v___x_181_);
v_args_140_ = v___x_182_;
v_modified_141_ = v_modified_177_;
v___y_142_ = v_a_97_;
goto v___jp_139_;
}
else
{
lean_dec(v_a_179_);
v_args_140_ = v_args_95_;
v_modified_141_ = v_modified_173_;
v___y_142_ = v_a_97_;
goto v___jp_139_;
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_args_95_);
v_a_183_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_178_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
lean_dec_ref(v___y_106_);
goto v___jp_101_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v___y_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
v___jp_109_:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_111_, v___y_110_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_130_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_130_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_unbox(v_a_115_);
lean_dec(v_a_115_);
if (v___x_119_ == 0)
{
lean_del_object(v___x_117_);
v___y_105_ = v___y_112_;
v___y_106_ = v___y_113_;
goto v___jp_104_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_fget_borrowed(v___y_113_, v___x_120_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Int_mkType;
v___x_125_ = lean_array_fset(v___y_113_, v___x_120_, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_126_);
v___x_128_ = v___x_117_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_del_object(v___x_117_);
v___y_105_ = v___y_112_;
v___y_106_ = v___y_113_;
goto v___jp_104_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v___y_113_);
v_a_131_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_114_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_114_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v_inst_144_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(2u);
v_inst_144_ = lean_array_fget_borrowed(v_args_140_, v___x_143_);
lean_inc(v_inst_144_);
v___x_145_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_144_, v___y_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_161_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_161_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_161_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_161_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v_a_146_);
lean_dec(v_a_146_);
if (v___x_150_ == 0)
{
lean_inc(v_inst_144_);
lean_del_object(v___x_148_);
v___y_110_ = v___y_142_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
v___y_113_ = v_args_140_;
goto v___jp_109_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_fget_borrowed(v_args_140_, v___x_151_);
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_154_ = l_Lean_Expr_isConstOf(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_155_ = l_Lean_Nat_mkType;
v___x_156_ = lean_array_fset(v_args_140_, v___x_151_, v___x_155_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_157_);
v___x_159_ = v___x_148_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_inc(v_inst_144_);
lean_del_object(v___x_148_);
v___y_110_ = v___y_142_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
v___y_113_ = v_args_140_;
goto v___jp_109_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v_args_140_);
v_a_162_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_145_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_145_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(lean_object* v_args_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_args_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_200_, lean_object* v_k_201_, uint8_t v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
if (v_a_202_ == 0)
{
lean_object* v___x_210_; lean_object* v_canon_211_; lean_object* v_cache_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = lean_st_ref_get(v_a_204_);
v_canon_211_ = lean_ctor_get(v___x_210_, 9);
lean_inc_ref(v_canon_211_);
lean_dec(v___x_210_);
v_cache_212_ = lean_ctor_get(v_canon_211_, 0);
lean_inc_ref(v_cache_212_);
lean_dec_ref(v_canon_211_);
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_200_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_213_, v___x_214_, v_cache_212_, v_e_200_);
lean_dec_ref(v_cache_212_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v_val_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_k_201_);
lean_dec_ref(v_e_200_);
v_val_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_val_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 0);
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_val_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v___x_215_);
v___x_224_ = lean_box(v_a_202_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
v___x_225_ = lean_apply_8(v_k_201_, v___x_224_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_329_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_329_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_329_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_329_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v_canon_231_; lean_object* v_share_232_; lean_object* v_maxFVar_233_; lean_object* v_proofInstInfo_234_; lean_object* v_inferType_235_; lean_object* v_getLevel_236_; lean_object* v_congrInfo_237_; lean_object* v_defEqI_238_; lean_object* v_extensions_239_; lean_object* v_issues_240_; lean_object* v_instanceOverrides_241_; uint8_t v_debug_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_328_; 
v___x_230_ = lean_st_ref_take(v_a_204_);
v_canon_231_ = lean_ctor_get(v___x_230_, 9);
v_share_232_ = lean_ctor_get(v___x_230_, 0);
v_maxFVar_233_ = lean_ctor_get(v___x_230_, 1);
v_proofInstInfo_234_ = lean_ctor_get(v___x_230_, 2);
v_inferType_235_ = lean_ctor_get(v___x_230_, 3);
v_getLevel_236_ = lean_ctor_get(v___x_230_, 4);
v_congrInfo_237_ = lean_ctor_get(v___x_230_, 5);
v_defEqI_238_ = lean_ctor_get(v___x_230_, 6);
v_extensions_239_ = lean_ctor_get(v___x_230_, 7);
v_issues_240_ = lean_ctor_get(v___x_230_, 8);
v_instanceOverrides_241_ = lean_ctor_get(v___x_230_, 10);
v_debug_242_ = lean_ctor_get_uint8(v___x_230_, sizeof(void*)*11);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_328_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_328_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_instanceOverrides_241_);
lean_inc(v_canon_231_);
lean_inc(v_issues_240_);
lean_inc(v_extensions_239_);
lean_inc(v_defEqI_238_);
lean_inc(v_congrInfo_237_);
lean_inc(v_getLevel_236_);
lean_inc(v_inferType_235_);
lean_inc(v_proofInstInfo_234_);
lean_inc(v_maxFVar_233_);
lean_inc(v_share_232_);
lean_dec(v___x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_328_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_cache_246_; lean_object* v_cacheInType_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_327_; 
v_cache_246_ = lean_ctor_get(v_canon_231_, 0);
v_cacheInType_247_ = lean_ctor_get(v_canon_231_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_canon_231_);
if (v_isSharedCheck_327_ == 0)
{
v___x_249_ = v_canon_231_;
v_isShared_250_ = v_isSharedCheck_327_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cacheInType_247_);
lean_inc(v_cache_246_);
lean_dec(v_canon_231_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_327_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___y_252_; lean_object* v___y_264_; lean_object* v_i_265_; lean_object* v___y_271_; lean_object* v___y_281_; lean_object* v_i_282_; lean_object* v___x_297_; 
lean_inc_ref(v_e_200_);
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_213_, v___x_214_, v_cache_246_, v_e_200_);
switch(lean_obj_tag(v___x_297_))
{
case 0:
{
lean_object* v_index_298_; lean_object* v_size_299_; lean_object* v___x_300_; 
v_index_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_298_);
lean_dec_ref_known(v___x_297_, 3);
v_size_299_ = lean_ctor_get(v_cache_246_, 0);
lean_inc(v_size_299_);
lean_inc(v_a_226_);
v___x_300_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_246_, v_size_299_, v_index_298_, v_e_200_, v_a_226_);
lean_dec(v_index_298_);
v___y_252_ = v___x_300_;
goto v___jp_251_;
}
case 1:
{
lean_object* v_index_301_; lean_object* v_size_302_; lean_object* v_keyArray_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_index_301_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_301_);
lean_dec_ref_known(v___x_297_, 1);
v_size_302_ = lean_ctor_get(v_cache_246_, 0);
v_keyArray_303_ = lean_ctor_get(v_cache_246_, 1);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_size_302_, v___x_304_);
v___x_306_ = lean_array_get_size(v_keyArray_303_);
v___x_307_ = lean_nat_dec_lt(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v___x_305_);
lean_dec(v_index_301_);
goto v___jp_287_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_mul(v___x_305_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(3u);
v___x_311_ = lean_nat_mul(v___x_306_, v___x_310_);
v___x_312_ = lean_nat_dec_le(v___x_309_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v___x_309_);
if (v___x_312_ == 0)
{
lean_dec(v___x_305_);
lean_dec(v_index_301_);
goto v___jp_287_;
}
else
{
lean_object* v___x_313_; 
lean_inc(v_a_226_);
v___x_313_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_246_, v___x_305_, v_index_301_, v_e_200_, v_a_226_);
lean_dec(v_index_301_);
v___y_252_ = v___x_313_;
goto v___jp_251_;
}
}
}
default: 
{
lean_object* v_size_314_; lean_object* v_keyArray_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_size_314_ = lean_ctor_get(v_cache_246_, 0);
v_keyArray_315_ = lean_ctor_get(v_cache_246_, 1);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_size_314_, v___x_316_);
v___x_318_ = lean_array_get_size(v_keyArray_315_);
v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec(v___x_317_);
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_213_, v___x_214_, v_cache_246_);
v___y_271_ = v___x_320_;
goto v___jp_270_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_321_ = lean_unsigned_to_nat(4u);
v___x_322_ = lean_nat_mul(v___x_317_, v___x_321_);
lean_dec(v___x_317_);
v___x_323_ = lean_unsigned_to_nat(3u);
v___x_324_ = lean_nat_mul(v___x_318_, v___x_323_);
v___x_325_ = lean_nat_dec_le(v___x_322_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v___x_322_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_213_, v___x_214_, v_cache_246_);
v___y_271_ = v___x_326_;
goto v___jp_270_;
}
else
{
v___y_271_ = v_cache_246_;
goto v___jp_270_;
}
}
}
}
v___jp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___y_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___y_252_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_cacheInType_247_);
v___x_254_ = v_reuseFailAlloc_262_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 9, v___x_254_);
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_share_232_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_maxFVar_233_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_proofInstInfo_234_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_inferType_235_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_getLevel_236_);
lean_ctor_set(v_reuseFailAlloc_261_, 5, v_congrInfo_237_);
lean_ctor_set(v_reuseFailAlloc_261_, 6, v_defEqI_238_);
lean_ctor_set(v_reuseFailAlloc_261_, 7, v_extensions_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 8, v_issues_240_);
lean_ctor_set(v_reuseFailAlloc_261_, 9, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 10, v_instanceOverrides_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*11, v_debug_242_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_st_ref_put(v_a_204_, v___x_256_);
if (v_isShared_229_ == 0)
{
v___x_259_ = v___x_228_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_226_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
v___jp_263_:
{
lean_object* v_size_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_size_266_ = lean_ctor_get(v___y_264_, 0);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_size_266_, v___x_267_);
lean_inc(v_a_226_);
v___x_269_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_264_, v___x_268_, v_i_265_, v_e_200_, v_a_226_);
lean_dec(v_i_265_);
v___y_252_ = v___x_269_;
goto v___jp_251_;
}
v___jp_270_:
{
lean_object* v___x_272_; 
lean_inc_ref(v_e_200_);
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_213_, v___x_214_, v___y_271_, v_e_200_);
switch(lean_obj_tag(v___x_272_))
{
case 0:
{
lean_object* v_index_273_; lean_object* v_size_274_; lean_object* v___x_275_; 
v_index_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_index_273_);
lean_dec_ref_known(v___x_272_, 3);
v_size_274_ = lean_ctor_get(v___y_271_, 0);
lean_inc(v_size_274_);
lean_inc(v_a_226_);
v___x_275_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_271_, v_size_274_, v_index_273_, v_e_200_, v_a_226_);
lean_dec(v_index_273_);
v___y_252_ = v___x_275_;
goto v___jp_251_;
}
case 1:
{
lean_object* v_index_276_; 
v_index_276_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_index_276_);
lean_dec_ref_known(v___x_272_, 1);
v___y_264_ = v___y_271_;
v_i_265_ = v_index_276_;
goto v___jp_263_;
}
default: 
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_271_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_index_279_; 
v_index_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_index_279_);
lean_dec_ref_known(v___x_278_, 1);
v___y_264_ = v___y_271_;
v_i_265_ = v_index_279_;
goto v___jp_263_;
}
else
{
lean_dec_ref(v_e_200_);
v___y_252_ = v___y_271_;
goto v___jp_251_;
}
}
}
}
v___jp_280_:
{
lean_object* v_size_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_size_283_ = lean_ctor_get(v___y_281_, 0);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_size_283_, v___x_284_);
lean_inc(v_a_226_);
v___x_286_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_281_, v___x_285_, v_i_282_, v_e_200_, v_a_226_);
lean_dec(v_i_282_);
v___y_252_ = v___x_286_;
goto v___jp_251_;
}
v___jp_287_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_213_, v___x_214_, v_cache_246_);
lean_inc_ref(v_e_200_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_213_, v___x_214_, v___x_288_, v_e_200_);
switch(lean_obj_tag(v___x_289_))
{
case 0:
{
lean_object* v_index_290_; lean_object* v_size_291_; lean_object* v___x_292_; 
v_index_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_289_, 3);
v_size_291_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_size_291_);
lean_inc(v_a_226_);
v___x_292_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_288_, v_size_291_, v_index_290_, v_e_200_, v_a_226_);
lean_dec(v_index_290_);
v___y_252_ = v___x_292_;
goto v___jp_251_;
}
case 1:
{
lean_object* v_index_293_; 
v_index_293_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_293_);
lean_dec_ref_known(v___x_289_, 1);
v___y_281_ = v___x_288_;
v_i_282_ = v_index_293_;
goto v___jp_280_;
}
default: 
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_288_, v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_index_296_; 
v_index_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_295_, 1);
v___y_281_ = v___x_288_;
v_i_282_ = v_index_296_;
goto v___jp_280_;
}
else
{
lean_dec_ref(v_e_200_);
v___y_252_ = v___x_288_;
goto v___jp_251_;
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
lean_dec_ref(v_e_200_);
return v___x_225_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v_canon_331_; lean_object* v_cacheInType_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_st_ref_get(v_a_204_);
v_canon_331_ = lean_ctor_get(v___x_330_, 9);
lean_inc_ref(v_canon_331_);
lean_dec(v___x_330_);
v_cacheInType_332_ = lean_ctor_get(v_canon_331_, 1);
lean_inc_ref(v_cacheInType_332_);
lean_dec_ref(v_canon_331_);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_200_);
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_333_, v___x_334_, v_cacheInType_332_, v_e_200_);
lean_dec_ref(v_cacheInType_332_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_k_201_);
lean_dec_ref(v_e_200_);
v_val_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 0);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_val_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_335_);
v___x_344_ = lean_box(v_a_202_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
v___x_345_ = lean_apply_8(v_k_201_, v___x_344_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_449_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_449_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_449_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_449_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v_canon_351_; lean_object* v_share_352_; lean_object* v_maxFVar_353_; lean_object* v_proofInstInfo_354_; lean_object* v_inferType_355_; lean_object* v_getLevel_356_; lean_object* v_congrInfo_357_; lean_object* v_defEqI_358_; lean_object* v_extensions_359_; lean_object* v_issues_360_; lean_object* v_instanceOverrides_361_; uint8_t v_debug_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_448_; 
v___x_350_ = lean_st_ref_take(v_a_204_);
v_canon_351_ = lean_ctor_get(v___x_350_, 9);
v_share_352_ = lean_ctor_get(v___x_350_, 0);
v_maxFVar_353_ = lean_ctor_get(v___x_350_, 1);
v_proofInstInfo_354_ = lean_ctor_get(v___x_350_, 2);
v_inferType_355_ = lean_ctor_get(v___x_350_, 3);
v_getLevel_356_ = lean_ctor_get(v___x_350_, 4);
v_congrInfo_357_ = lean_ctor_get(v___x_350_, 5);
v_defEqI_358_ = lean_ctor_get(v___x_350_, 6);
v_extensions_359_ = lean_ctor_get(v___x_350_, 7);
v_issues_360_ = lean_ctor_get(v___x_350_, 8);
v_instanceOverrides_361_ = lean_ctor_get(v___x_350_, 10);
v_debug_362_ = lean_ctor_get_uint8(v___x_350_, sizeof(void*)*11);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_448_ == 0)
{
v___x_364_ = v___x_350_;
v_isShared_365_ = v_isSharedCheck_448_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_instanceOverrides_361_);
lean_inc(v_canon_351_);
lean_inc(v_issues_360_);
lean_inc(v_extensions_359_);
lean_inc(v_defEqI_358_);
lean_inc(v_congrInfo_357_);
lean_inc(v_getLevel_356_);
lean_inc(v_inferType_355_);
lean_inc(v_proofInstInfo_354_);
lean_inc(v_maxFVar_353_);
lean_inc(v_share_352_);
lean_dec(v___x_350_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_448_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_cache_366_; lean_object* v_cacheInType_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_447_; 
v_cache_366_ = lean_ctor_get(v_canon_351_, 0);
v_cacheInType_367_ = lean_ctor_get(v_canon_351_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_canon_351_);
if (v_isSharedCheck_447_ == 0)
{
v___x_369_ = v_canon_351_;
v_isShared_370_ = v_isSharedCheck_447_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_cacheInType_367_);
lean_inc(v_cache_366_);
lean_dec(v_canon_351_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_447_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___y_372_; lean_object* v___y_384_; lean_object* v_i_385_; lean_object* v___y_401_; lean_object* v_i_402_; lean_object* v___y_408_; lean_object* v___x_417_; 
lean_inc_ref(v_e_200_);
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_333_, v___x_334_, v_cacheInType_367_, v_e_200_);
switch(lean_obj_tag(v___x_417_))
{
case 0:
{
lean_object* v_index_418_; lean_object* v_size_419_; lean_object* v___x_420_; 
v_index_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_418_);
lean_dec_ref_known(v___x_417_, 3);
v_size_419_ = lean_ctor_get(v_cacheInType_367_, 0);
lean_inc(v_size_419_);
lean_inc(v_a_346_);
v___x_420_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_367_, v_size_419_, v_index_418_, v_e_200_, v_a_346_);
lean_dec(v_index_418_);
v___y_372_ = v___x_420_;
goto v___jp_371_;
}
case 1:
{
lean_object* v_index_421_; lean_object* v_size_422_; lean_object* v_keyArray_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_index_421_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_421_);
lean_dec_ref_known(v___x_417_, 1);
v_size_422_ = lean_ctor_get(v_cacheInType_367_, 0);
v_keyArray_423_ = lean_ctor_get(v_cacheInType_367_, 1);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_size_422_, v___x_424_);
v___x_426_ = lean_array_get_size(v_keyArray_423_);
v___x_427_ = lean_nat_dec_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v___x_425_);
lean_dec(v_index_421_);
goto v___jp_390_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_428_ = lean_unsigned_to_nat(4u);
v___x_429_ = lean_nat_mul(v___x_425_, v___x_428_);
v___x_430_ = lean_unsigned_to_nat(3u);
v___x_431_ = lean_nat_mul(v___x_426_, v___x_430_);
v___x_432_ = lean_nat_dec_le(v___x_429_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v___x_429_);
if (v___x_432_ == 0)
{
lean_dec(v___x_425_);
lean_dec(v_index_421_);
goto v___jp_390_;
}
else
{
lean_object* v___x_433_; 
lean_inc(v_a_346_);
v___x_433_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_367_, v___x_425_, v_index_421_, v_e_200_, v_a_346_);
lean_dec(v_index_421_);
v___y_372_ = v___x_433_;
goto v___jp_371_;
}
}
}
default: 
{
lean_object* v_size_434_; lean_object* v_keyArray_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_size_434_ = lean_ctor_get(v_cacheInType_367_, 0);
v_keyArray_435_ = lean_ctor_get(v_cacheInType_367_, 1);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_size_434_, v___x_436_);
v___x_438_ = lean_array_get_size(v_keyArray_435_);
v___x_439_ = lean_nat_dec_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec(v___x_437_);
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_333_, v___x_334_, v_cacheInType_367_);
v___y_408_ = v___x_440_;
goto v___jp_407_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_441_ = lean_unsigned_to_nat(4u);
v___x_442_ = lean_nat_mul(v___x_437_, v___x_441_);
lean_dec(v___x_437_);
v___x_443_ = lean_unsigned_to_nat(3u);
v___x_444_ = lean_nat_mul(v___x_438_, v___x_443_);
v___x_445_ = lean_nat_dec_le(v___x_442_, v___x_444_);
lean_dec(v___x_444_);
lean_dec(v___x_442_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_333_, v___x_334_, v_cacheInType_367_);
v___y_408_ = v___x_446_;
goto v___jp_407_;
}
else
{
v___y_408_ = v_cacheInType_367_;
goto v___jp_407_;
}
}
}
}
v___jp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___y_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_cache_366_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___y_372_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 9, v___x_374_);
v___x_376_ = v___x_364_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_share_352_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_maxFVar_353_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_proofInstInfo_354_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_inferType_355_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_getLevel_356_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_congrInfo_357_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_defEqI_358_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_extensions_359_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v_issues_360_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 10, v_instanceOverrides_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*11, v_debug_362_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_put(v_a_204_, v___x_376_);
if (v_isShared_349_ == 0)
{
v___x_379_ = v___x_348_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_346_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
v___jp_383_:
{
lean_object* v_size_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_size_386_ = lean_ctor_get(v___y_384_, 0);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_size_386_, v___x_387_);
lean_inc(v_a_346_);
v___x_389_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_384_, v___x_388_, v_i_385_, v_e_200_, v_a_346_);
lean_dec(v_i_385_);
v___y_372_ = v___x_389_;
goto v___jp_371_;
}
v___jp_390_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_333_, v___x_334_, v_cacheInType_367_);
lean_inc_ref(v_e_200_);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_333_, v___x_334_, v___x_391_, v_e_200_);
switch(lean_obj_tag(v___x_392_))
{
case 0:
{
lean_object* v_index_393_; lean_object* v_size_394_; lean_object* v___x_395_; 
v_index_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_index_393_);
lean_dec_ref_known(v___x_392_, 3);
v_size_394_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_size_394_);
lean_inc(v_a_346_);
v___x_395_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_391_, v_size_394_, v_index_393_, v_e_200_, v_a_346_);
lean_dec(v_index_393_);
v___y_372_ = v___x_395_;
goto v___jp_371_;
}
case 1:
{
lean_object* v_index_396_; 
v_index_396_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_index_396_);
lean_dec_ref_known(v___x_392_, 1);
v___y_384_ = v___x_391_;
v_i_385_ = v_index_396_;
goto v___jp_383_;
}
default: 
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_391_, v___x_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_index_399_; 
v_index_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_index_399_);
lean_dec_ref_known(v___x_398_, 1);
v___y_384_ = v___x_391_;
v_i_385_ = v_index_399_;
goto v___jp_383_;
}
else
{
lean_dec_ref(v_e_200_);
v___y_372_ = v___x_391_;
goto v___jp_371_;
}
}
}
}
v___jp_400_:
{
lean_object* v_size_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_size_403_ = lean_ctor_get(v___y_401_, 0);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_size_403_, v___x_404_);
lean_inc(v_a_346_);
v___x_406_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_401_, v___x_405_, v_i_402_, v_e_200_, v_a_346_);
lean_dec(v_i_402_);
v___y_372_ = v___x_406_;
goto v___jp_371_;
}
v___jp_407_:
{
lean_object* v___x_409_; 
lean_inc_ref(v_e_200_);
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_333_, v___x_334_, v___y_408_, v_e_200_);
switch(lean_obj_tag(v___x_409_))
{
case 0:
{
lean_object* v_index_410_; lean_object* v_size_411_; lean_object* v___x_412_; 
v_index_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_410_);
lean_dec_ref_known(v___x_409_, 3);
v_size_411_ = lean_ctor_get(v___y_408_, 0);
lean_inc(v_size_411_);
lean_inc(v_a_346_);
v___x_412_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_408_, v_size_411_, v_index_410_, v_e_200_, v_a_346_);
lean_dec(v_index_410_);
v___y_372_ = v___x_412_;
goto v___jp_371_;
}
case 1:
{
lean_object* v_index_413_; 
v_index_413_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_413_);
lean_dec_ref_known(v___x_409_, 1);
v___y_401_ = v___y_408_;
v_i_402_ = v_index_413_;
goto v___jp_400_;
}
default: 
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_408_, v___x_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_index_416_; 
v_index_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_index_416_);
lean_dec_ref_known(v___x_415_, 1);
v___y_401_ = v___y_408_;
v_i_402_ = v_index_416_;
goto v___jp_400_;
}
else
{
lean_dec_ref(v_e_200_);
v___y_372_ = v___y_408_;
goto v___jp_371_;
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
lean_dec_ref(v_e_200_);
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_450_, lean_object* v_k_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
uint8_t v_a_boxed_460_; lean_object* v_res_461_; 
v_a_boxed_460_ = lean_unbox(v_a_452_);
v_res_461_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_450_, v_k_451_, v_a_boxed_460_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_461_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Expr_cleanupAnnotations(v_e_468_);
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_471_ = l_Lean_Expr_isConstOf(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_Expr_isApp(v___x_469_);
if (v___x_472_ == 0)
{
lean_dec_ref(v___x_469_);
return v___x_472_;
}
else
{
lean_object* v_arg_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_arg_473_ = lean_ctor_get(v___x_469_, 1);
lean_inc_ref(v_arg_473_);
v___x_474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_469_);
v___x_475_ = l_Lean_Expr_isApp(v___x_474_);
if (v___x_475_ == 0)
{
lean_dec_ref(v___x_474_);
lean_dec_ref(v_arg_473_);
return v___x_475_;
}
else
{
lean_object* v_arg_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_arg_476_ = lean_ctor_get(v___x_474_, 1);
lean_inc_ref(v_arg_476_);
v___x_477_ = l_Lean_Expr_appFnCleanup___redArg(v___x_474_);
v___x_478_ = l_Lean_Expr_isApp(v___x_477_);
if (v___x_478_ == 0)
{
lean_dec_ref(v___x_477_);
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_473_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = l_Lean_Expr_appFnCleanup___redArg(v___x_477_);
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_481_ = l_Lean_Expr_isConstOf(v___x_479_, v___x_480_);
lean_dec_ref(v___x_479_);
if (v___x_481_ == 0)
{
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_473_);
return v___x_481_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = l_Lean_Expr_isBoolTrue(v_arg_476_);
if (v___x_482_ == 0)
{
lean_dec_ref(v_arg_473_);
return v___x_482_;
}
else
{
uint8_t v___x_483_; 
v___x_483_ = l_Lean_Expr_isBoolTrue(v_arg_473_);
return v___x_483_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_469_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_484_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = l_Lean_Expr_cleanupAnnotations(v_e_490_);
v___x_492_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_493_ = l_Lean_Expr_isConstOf(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = l_Lean_Expr_isApp(v___x_491_);
if (v___x_494_ == 0)
{
lean_dec_ref(v___x_491_);
return v___x_494_;
}
else
{
lean_object* v_arg_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_arg_495_ = lean_ctor_get(v___x_491_, 1);
lean_inc_ref(v_arg_495_);
v___x_496_ = l_Lean_Expr_appFnCleanup___redArg(v___x_491_);
v___x_497_ = l_Lean_Expr_isApp(v___x_496_);
if (v___x_497_ == 0)
{
lean_dec_ref(v___x_496_);
lean_dec_ref(v_arg_495_);
return v___x_497_;
}
else
{
lean_object* v_arg_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_arg_498_ = lean_ctor_get(v___x_496_, 1);
lean_inc_ref(v_arg_498_);
v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_496_);
v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
if (v___x_500_ == 0)
{
lean_dec_ref(v___x_499_);
lean_dec_ref(v_arg_498_);
lean_dec_ref(v_arg_495_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_503_ = l_Lean_Expr_isConstOf(v___x_501_, v___x_502_);
lean_dec_ref(v___x_501_);
if (v___x_503_ == 0)
{
lean_dec_ref(v_arg_498_);
lean_dec_ref(v_arg_495_);
return v___x_503_;
}
else
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Expr_isBoolFalse(v_arg_498_);
if (v___x_504_ == 0)
{
lean_dec_ref(v_arg_495_);
return v___x_504_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_Expr_isBoolTrue(v_arg_495_);
return v___x_505_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_491_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_509_){
_start:
{
switch(v_x_509_)
{
case 0:
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
return v___x_510_;
}
case 1:
{
lean_object* v___x_511_; 
v___x_511_ = lean_unsigned_to_nat(1u);
return v___x_511_;
}
case 2:
{
lean_object* v___x_512_; 
v___x_512_ = lean_unsigned_to_nat(2u);
return v___x_512_;
}
default: 
{
lean_object* v___x_513_; 
v___x_513_ = lean_unsigned_to_nat(3u);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_514_){
_start:
{
uint8_t v_x_boxed_515_; lean_object* v_res_516_; 
v_x_boxed_515_ = lean_unbox(v_x_514_);
v_res_516_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_517_){
_start:
{
lean_inc(v_k_517_);
return v_k_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_518_);
lean_dec(v_k_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_520_, lean_object* v_ctorIdx_521_, uint8_t v_t_522_, lean_object* v_h_523_, lean_object* v_k_524_){
_start:
{
lean_inc(v_k_524_);
return v_k_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_525_, lean_object* v_ctorIdx_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_k_529_){
_start:
{
uint8_t v_t_boxed_530_; lean_object* v_res_531_; 
v_t_boxed_530_ = lean_unbox(v_t_527_);
v_res_531_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_525_, v_ctorIdx_526_, v_t_boxed_530_, v_h_528_, v_k_529_);
lean_dec(v_k_529_);
lean_dec(v_ctorIdx_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_532_){
_start:
{
lean_inc(v_canonType_532_);
return v_canonType_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_533_);
lean_dec(v_canonType_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_535_, uint8_t v_t_536_, lean_object* v_h_537_, lean_object* v_canonType_538_){
_start:
{
lean_inc(v_canonType_538_);
return v_canonType_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_canonType_542_){
_start:
{
uint8_t v_t_boxed_543_; lean_object* v_res_544_; 
v_t_boxed_543_ = lean_unbox(v_t_540_);
v_res_544_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_539_, v_t_boxed_543_, v_h_541_, v_canonType_542_);
lean_dec(v_canonType_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_545_){
_start:
{
lean_inc(v_canonInst_545_);
return v_canonInst_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_546_);
lean_dec(v_canonInst_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_548_, uint8_t v_t_549_, lean_object* v_h_550_, lean_object* v_canonInst_551_){
_start:
{
lean_inc(v_canonInst_551_);
return v_canonInst_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_canonInst_555_){
_start:
{
uint8_t v_t_boxed_556_; lean_object* v_res_557_; 
v_t_boxed_556_ = lean_unbox(v_t_553_);
v_res_557_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_552_, v_t_boxed_556_, v_h_554_, v_canonInst_555_);
lean_dec(v_canonInst_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_558_){
_start:
{
lean_inc(v_canonImplicit_558_);
return v_canonImplicit_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_559_);
lean_dec(v_canonImplicit_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_561_, uint8_t v_t_562_, lean_object* v_h_563_, lean_object* v_canonImplicit_564_){
_start:
{
lean_inc(v_canonImplicit_564_);
return v_canonImplicit_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_canonImplicit_568_){
_start:
{
uint8_t v_t_boxed_569_; lean_object* v_res_570_; 
v_t_boxed_569_ = lean_unbox(v_t_566_);
v_res_570_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_565_, v_t_boxed_569_, v_h_567_, v_canonImplicit_568_);
lean_dec(v_canonImplicit_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_571_){
_start:
{
lean_inc(v_visit_571_);
return v_visit_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_572_);
lean_dec(v_visit_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_574_, uint8_t v_t_575_, lean_object* v_h_576_, lean_object* v_visit_577_){
_start:
{
lean_inc(v_visit_577_);
return v_visit_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_visit_581_){
_start:
{
uint8_t v_t_boxed_582_; lean_object* v_res_583_; 
v_t_boxed_582_ = lean_unbox(v_t_579_);
v_res_583_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_578_, v_t_boxed_582_, v_h_580_, v_visit_581_);
lean_dec(v_visit_581_);
return v_res_583_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = 0;
return v___x_584_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = 0;
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_598_, lean_object* v_x_599_){
_start:
{
switch(v_r_598_)
{
case 0:
{
lean_object* v___x_600_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_600_;
}
case 1:
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_601_;
}
case 2:
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_602_;
}
default: 
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_604_, lean_object* v_x_605_){
_start:
{
uint8_t v_r_boxed_606_; lean_object* v_res_607_; 
v_r_boxed_606_ = lean_unbox(v_r_604_);
v_res_607_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_606_, v_x_605_);
lean_dec(v_x_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_610_, lean_object* v_i_611_, lean_object* v_arg_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_pinfos_610_);
v___x_669_ = lean_nat_dec_lt(v_i_611_, v___x_668_);
if (v___x_669_ == 0)
{
v___y_619_ = v_a_613_;
v___y_620_ = v_a_614_;
v___y_621_ = v_a_615_;
v___y_622_ = v_a_616_;
goto v___jp_618_;
}
else
{
lean_object* v_pinfo_670_; uint8_t v_isInstance_671_; 
v_pinfo_670_ = lean_array_fget_borrowed(v_pinfos_610_, v_i_611_);
v_isInstance_671_ = lean_ctor_get_uint8(v_pinfo_670_, sizeof(void*)*1 + 4);
if (v_isInstance_671_ == 0)
{
uint8_t v_isProp_672_; 
v_isProp_672_ = lean_ctor_get_uint8(v_pinfo_670_, sizeof(void*)*1 + 2);
if (v_isProp_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_670_);
if (v___x_673_ == 0)
{
v___y_619_ = v_a_613_;
v___y_620_ = v_a_614_;
v___y_621_ = v_a_615_;
v___y_622_ = v_a_616_;
goto v___jp_618_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Meta_isTypeFormer(v_arg_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_690_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_690_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_unbox(v_a_675_);
lean_dec(v_a_675_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = 2;
v___x_681_ = lean_box(v___x_680_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_683_ = v___x_677_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_685_ = 0;
v___x_686_ = lean_box(v___x_685_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_686_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
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
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_674_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_674_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
else
{
uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref(v_arg_612_);
v___x_699_ = 3;
v___x_700_ = lean_box(v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
else
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v_arg_612_);
v___x_702_ = 1;
v___x_703_ = lean_box(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
v___jp_618_:
{
lean_object* v___x_623_; 
lean_inc_ref(v_arg_612_);
v___x_623_ = l_Lean_Meta_isProp(v_arg_612_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_659_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_659_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_659_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_659_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; 
v___x_628_ = lean_unbox(v_a_624_);
lean_dec(v_a_624_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_del_object(v___x_626_);
v___x_629_ = l_Lean_Meta_isTypeFormer(v_arg_612_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_645_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_645_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
uint8_t v___x_634_; 
v___x_634_ = lean_unbox(v_a_630_);
lean_dec(v_a_630_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = 3;
v___x_636_ = lean_box(v___x_635_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_638_ = v___x_632_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = 0;
v___x_641_ = lean_box(v___x_640_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_641_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_a_646_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_629_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_629_);
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
else
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec_ref(v_arg_612_);
v___x_654_ = 3;
v___x_655_ = lean_box(v___x_654_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_655_);
v___x_657_ = v___x_626_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_arg_612_);
v_a_660_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_623_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_623_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_705_, lean_object* v_i_706_, lean_object* v_arg_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_705_, v_i_706_, v_arg_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_i_706_);
lean_dec_ref(v_pinfos_705_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_714_, lean_object* v_offset_715_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_nat_dec_eq(v_offset_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = l_Lean_mkNatLit(v_offset_715_);
v___x_719_ = l_Lean_mkNatAdd(v_e_714_, v___x_718_);
return v___x_719_;
}
else
{
lean_dec(v_offset_715_);
return v_e_714_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v_dummy_721_; 
v___x_720_ = lean_box(0);
v_dummy_721_ = l_Lean_Expr_sort___override(v___x_720_);
return v_dummy_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_722_, lean_object* v_e_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
uint8_t v_fromClass_729_; 
v_fromClass_729_ = lean_ctor_get_uint8(v_info_722_, sizeof(void*)*3);
if (v_fromClass_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_723_, v_fromClass_729_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_766_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_766_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_766_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_766_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_a_731_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_del_object(v___x_733_);
v_val_735_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v_a_731_, 1);
v___x_736_ = l_Lean_Expr_getAppFn(v_val_735_);
v___x_737_ = l_Lean_Meta_reduceProj_x3f(v___x_736_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
if (lean_obj_tag(v_a_738_) == 0)
{
lean_dec(v_val_735_);
return v___x_737_;
}
else
{
lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_760_; 
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_761_);
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
else
{
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_759_; 
v_val_742_ = lean_ctor_get(v_a_738_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_759_ == 0)
{
v___x_744_ = v_a_738_;
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_a_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_dummy_746_; lean_object* v_nargs_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_dummy_746_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_747_ = l_Lean_Expr_getAppNumArgs(v_val_735_);
lean_inc(v_nargs_747_);
v___x_748_ = lean_mk_array(v_nargs_747_, v_dummy_746_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_sub(v_nargs_747_, v___x_749_);
lean_dec(v_nargs_747_);
v___x_751_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_735_, v___x_748_, v___x_750_);
v___x_752_ = l_Lean_mkAppN(v_val_742_, v___x_751_);
lean_dec_ref(v___x_751_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_752_);
v___x_754_ = v___x_744_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_754_);
v___x_756_ = v___x_740_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
else
{
lean_dec(v_val_735_);
return v___x_737_;
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec(v_a_731_);
v___x_762_ = lean_box(0);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_762_);
v___x_764_ = v___x_733_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
return v___x_730_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_e_723_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_769_, lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_769_, v_e_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_info_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_777_, lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_777_, v_e_778_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_787_, lean_object* v_e_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_787_, v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec_ref(v_info_787_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_797_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_799_ = l_Lean_Expr_isConstOf(v_e_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_800_);
lean_dec_ref(v_e_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = l_Lean_Expr_cleanupAnnotations(v_e_836_);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_839_ = l_Lean_Expr_isConstOf(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Expr_isApp(v___x_837_);
if (v___x_840_ == 0)
{
lean_dec_ref(v___x_837_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = l_Lean_Expr_appFnCleanup___redArg(v___x_837_);
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_843_ = l_Lean_Expr_isConstOf(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Expr_isApp(v___x_841_);
if (v___x_844_ == 0)
{
lean_dec_ref(v___x_841_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_841_);
v___x_846_ = l_Lean_Expr_isApp(v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v___x_845_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_845_);
v___x_848_ = l_Lean_Expr_isApp(v___x_847_);
if (v___x_848_ == 0)
{
lean_dec_ref(v___x_847_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_847_);
v___x_850_ = l_Lean_Expr_isApp(v___x_849_);
if (v___x_850_ == 0)
{
lean_dec_ref(v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = l_Lean_Expr_appFnCleanup___redArg(v___x_849_);
v___x_852_ = l_Lean_Expr_isApp(v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v___x_851_);
return v___x_852_;
}
else
{
lean_object* v_arg_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_arg_853_ = lean_ctor_get(v___x_851_, 1);
lean_inc_ref(v_arg_853_);
v___x_854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_851_);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_856_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_858_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_860_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_862_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_864_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_863_);
lean_dec_ref(v___x_854_);
if (v___x_864_ == 0)
{
lean_dec_ref(v_arg_853_);
return v___x_864_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_853_);
lean_dec_ref(v_arg_853_);
return v___x_865_;
}
}
else
{
uint8_t v___x_866_; 
lean_dec_ref(v___x_854_);
v___x_866_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_853_);
lean_dec_ref(v_arg_853_);
return v___x_866_;
}
}
else
{
uint8_t v___x_867_; 
lean_dec_ref(v___x_854_);
v___x_867_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_853_);
lean_dec_ref(v_arg_853_);
return v___x_867_;
}
}
else
{
uint8_t v___x_868_; 
lean_dec_ref(v___x_854_);
v___x_868_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_853_);
lean_dec_ref(v_arg_853_);
return v___x_868_;
}
}
else
{
uint8_t v___x_869_; 
lean_dec_ref(v___x_854_);
v___x_869_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_853_);
lean_dec_ref(v_arg_853_);
return v___x_869_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_841_);
return v___x_843_;
}
}
}
else
{
lean_dec_ref(v___x_837_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_870_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_879_, lean_object* v_inst_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; 
lean_inc_ref(v_inst_880_);
lean_inc_ref(v_e_879_);
v___x_888_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_879_, v_inst_880_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_939_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_939_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_939_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_939_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
lean_del_object(v___x_891_);
v___x_894_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_881_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_927_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_927_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_927_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_927_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
uint8_t v_verbose_899_; 
v_verbose_899_ = lean_ctor_get_uint8(v_a_895_, 0);
lean_dec(v_a_895_);
if (v_verbose_899_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v_inst_880_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_e_879_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_e_879_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_897_);
v___x_903_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_879_);
v___x_904_ = l_Lean_indentExpr(v_e_879_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_indentExpr(v_inst_880_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Meta_Sym_reportIssue(v___x_909_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v___x_910_, 0);
lean_dec(v_unused_918_);
v___x_912_ = v___x_910_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_dec(v___x_910_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_e_879_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_e_879_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_e_879_);
v_a_919_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_910_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_910_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_inst_880_);
lean_dec_ref(v_e_879_);
v_a_928_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_894_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_894_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v_e_879_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_inst_880_);
v___x_937_ = v___x_891_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_inst_880_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_inst_880_);
lean_dec_ref(v_e_879_);
v_a_940_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_888_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_888_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_948_, lean_object* v_inst_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_948_, v_inst_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_env_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_st_ref_get(v___y_959_);
v_env_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_961_);
v___x_963_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_962_, v_declName_958_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_965_, v___y_966_);
lean_dec(v___y_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_969_, uint8_t v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_969_, v___y_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___y_4074__boxed_988_; lean_object* v_res_989_; 
v___y_4074__boxed_988_ = lean_unbox(v___y_980_);
v_res_989_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_979_, v___y_4074__boxed_988_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_990_, uint8_t v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
uint8_t v___x_999_; 
lean_inc_ref(v_e_990_);
v___x_999_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_990_);
if (v___x_999_ == 0)
{
lean_object* v_f_1000_; 
v_f_1000_ = l_Lean_Expr_getAppFn(v_e_990_);
if (lean_obj_tag(v_f_1000_) == 4)
{
lean_object* v_declName_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1032_; 
v_declName_1001_ = lean_ctor_get(v_f_1000_, 0);
lean_inc(v_declName_1001_);
lean_dec_ref_known(v_f_1000_, 2);
v___x_1002_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_1001_, v_a_997_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1032_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1032_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_a_1003_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_1005_);
v_val_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_a_1003_, 1);
lean_inc_ref(v_e_990_);
v___x_1008_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_1007_, v_e_990_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_val_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1020_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 0)
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_e_990_);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_e_990_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1018_; 
lean_dec_ref(v_e_990_);
v_val_1016_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v_a_1009_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_val_1016_);
v___x_1018_ = v___x_1011_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_val_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v_e_990_);
v_a_1021_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1008_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1008_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_e_990_);
v___x_1030_ = v___x_1005_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_e_990_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v_f_1000_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_e_990_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_inc_ref(v_e_990_);
v___x_1034_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_1034_, 0, v_e_990_);
v___x_1035_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_1034_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1069_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1069_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1069_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
if (lean_obj_tag(v_a_1036_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_dec_ref(v_e_990_);
v_val_1040_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_val_1040_);
lean_dec_ref_known(v_a_1036_, 1);
v___x_1041_ = l_Lean_mkNatLit(v_val_1040_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1043_ = v___x_1038_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
else
{
lean_object* v___x_1045_; 
lean_del_object(v___x_1038_);
lean_dec(v_a_1036_);
lean_inc_ref(v_e_990_);
v___x_1045_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_990_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1060_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
if (lean_obj_tag(v_a_1046_) == 1)
{
lean_object* v_val_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec_ref(v_e_990_);
v_val_1050_ = lean_ctor_get(v_a_1046_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v_a_1046_, 1);
v_fst_1051_ = lean_ctor_get(v_val_1050_, 0);
lean_inc(v_fst_1051_);
v_snd_1052_ = lean_ctor_get(v_val_1050_, 1);
lean_inc(v_snd_1052_);
lean_dec(v_val_1050_);
v___x_1053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_1051_, v_snd_1052_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1058_; 
lean_dec(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_e_990_);
v___x_1058_ = v___x_1048_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_e_990_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v_e_990_);
v_a_1061_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1045_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1045_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_e_990_);
v_a_1070_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1035_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1035_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
uint8_t v_a_boxed_1087_; lean_object* v_res_1088_; 
v_a_boxed_1087_ = lean_unbox(v_a_1079_);
v_res_1088_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_1078_, v_a_boxed_1087_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
return v_res_1088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1092_, lean_object* v_type_1093_, uint8_t v_report_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; 
lean_inc_ref(v_type_1093_);
v___x_1102_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1093_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1154_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1154_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1154_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
if (lean_obj_tag(v_a_1103_) == 1)
{
lean_object* v_val_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_1105_);
lean_dec_ref(v_type_1093_);
v_val_1107_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v_a_1103_, 1);
v___x_1108_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1092_, v_val_1107_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1108_;
}
else
{
lean_dec(v_a_1103_);
if (v_report_1094_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_type_1093_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_e_1092_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_e_1092_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v___x_1112_; 
lean_del_object(v___x_1105_);
v___x_1112_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1095_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1145_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1145_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1145_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v_verbose_1117_; 
v_verbose_1117_ = lean_ctor_get_uint8(v_a_1113_, 0);
lean_dec(v_a_1113_);
if (v_verbose_1117_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v_type_1093_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_e_1092_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_e_1092_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1115_);
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1092_);
v___x_1122_ = l_Lean_indentExpr(v_e_1092_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_indentExpr(v_type_1093_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_Meta_Sym_reportIssue(v___x_1127_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1128_, 0);
lean_dec(v_unused_1136_);
v___x_1130_ = v___x_1128_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v___x_1128_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_e_1092_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_e_1092_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_e_1092_);
v_a_1137_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1128_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1128_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_type_1093_);
lean_dec_ref(v_e_1092_);
v_a_1146_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1112_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1112_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_type_1093_);
lean_dec_ref(v_e_1092_);
v_a_1155_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1102_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1102_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1163_, lean_object* v_type_1164_, lean_object* v_report_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_report_boxed_1173_; lean_object* v_res_1174_; 
v_report_boxed_1173_ = lean_unbox(v_report_1165_);
v_res_1174_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1163_, v_type_1164_, v_report_boxed_1173_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1175_, lean_object* v_type_1176_, uint8_t v_report_1177_, uint8_t v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1175_, v_type_1176_, v_report_1177_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1187_, lean_object* v_type_1188_, lean_object* v_report_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_report_boxed_1198_; uint8_t v_a_boxed_1199_; lean_object* v_res_1200_; 
v_report_boxed_1198_ = lean_unbox(v_report_1189_);
v_a_boxed_1199_ = lean_unbox(v_a_1190_);
v_res_1200_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1187_, v_type_1188_, v_report_boxed_1198_, v_a_boxed_1199_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0(lean_object* v_k_1201_, uint8_t v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v_b_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_box(v___y_1202_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
v___x_1212_ = lean_apply_9(v_k_1201_, v_b_1205_, v___x_1211_, v___y_1203_, v___y_1204_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, lean_box(0));
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0___boxed(lean_object* v_k_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v___y_70838__boxed_1223_; lean_object* v_res_1224_; 
v___y_70838__boxed_1223_ = lean_unbox(v___y_1214_);
v_res_1224_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0(v_k_1213_, v___y_70838__boxed_1223_, v___y_1215_, v___y_1216_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(lean_object* v_name_1225_, uint8_t v_bi_1226_, lean_object* v_type_1227_, lean_object* v_k_1228_, uint8_t v_kind_1229_, uint8_t v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_box(v___y_1230_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1239_, 0, v_k_1228_);
lean_closure_set(v___f_1239_, 1, v___x_1238_);
lean_closure_set(v___f_1239_, 2, v___y_1231_);
lean_closure_set(v___f_1239_, 3, v___y_1232_);
v___x_1240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1225_, v_bi_1226_, v_type_1227_, v___f_1239_, v_kind_1229_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1240_) == 0)
{
return v___x_1240_;
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg___boxed(lean_object* v_name_1249_, lean_object* v_bi_1250_, lean_object* v_type_1251_, lean_object* v_k_1252_, lean_object* v_kind_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_bi_boxed_1262_; uint8_t v_kind_boxed_1263_; uint8_t v___y_70866__boxed_1264_; lean_object* v_res_1265_; 
v_bi_boxed_1262_ = lean_unbox(v_bi_1250_);
v_kind_boxed_1263_ = lean_unbox(v_kind_1253_);
v___y_70866__boxed_1264_ = lean_unbox(v___y_1254_);
v_res_1265_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(v_name_1249_, v_bi_boxed_1262_, v_type_1251_, v_k_1252_, v_kind_boxed_1263_, v___y_70866__boxed_1264_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_m_1266_, lean_object* v_query_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v_zero_1271_; uint8_t v_isZero_1272_; 
v_zero_1271_ = lean_unsigned_to_nat(0u);
v_isZero_1272_ = lean_nat_dec_eq(v_x_1269_, v_zero_1271_);
if (v_isZero_1272_ == 1)
{
lean_dec(v_x_1270_);
lean_dec(v_x_1269_);
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_box(2);
return v___x_1273_;
}
else
{
lean_object* v_val_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_val_1274_ = lean_ctor_get(v_x_1268_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v_x_1268_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_val_1274_);
lean_dec(v_x_1268_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_val_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_keyArray_1282_; lean_object* v_valueArray_1283_; lean_object* v___x_1284_; uint8_t v_isSome_1285_; 
v_keyArray_1282_ = lean_ctor_get(v_m_1266_, 1);
v_valueArray_1283_ = lean_ctor_get(v_m_1266_, 2);
v___x_1284_ = lean_array_fget_borrowed(v_keyArray_1282_, v_x_1270_);
v_isSome_1285_ = lean_noption_is_some(v___x_1284_);
if (v_isSome_1285_ == 0)
{
lean_dec(v_x_1269_);
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_x_1270_);
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_x_1270_);
v_val_1287_ = lean_ctor_get(v_x_1268_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v_x_1268_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v_x_1268_);
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
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_one_1295_; lean_object* v_n_1296_; lean_object* v___y_1298_; 
v_one_1295_ = lean_unsigned_to_nat(1u);
v_n_1296_ = lean_nat_sub(v_x_1269_, v_one_1295_);
lean_dec(v_x_1269_);
if (v_isSome_1285_ == 0)
{
goto v___jp_1304_;
}
else
{
lean_object* v___x_1306_; uint8_t v_isSome_1307_; 
v___x_1306_ = lean_array_fget_borrowed(v_valueArray_1283_, v_x_1270_);
v_isSome_1307_ = lean_noption_is_some(v___x_1306_);
if (v_isSome_1307_ == 0)
{
goto v___jp_1304_;
}
else
{
lean_object* v_val_1308_; uint8_t v___x_1309_; 
lean_inc(v___x_1284_);
v_val_1308_ = lean_noption_get(v___x_1284_);
v___x_1309_ = lean_expr_eqv(v_val_1308_, v_query_1267_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
lean_dec(v_val_1308_);
v___x_1310_ = lean_array_get_size(v_keyArray_1282_);
v___x_1311_ = lean_nat_add(v_x_1270_, v_one_1295_);
lean_dec(v_x_1270_);
v___x_1312_ = lean_nat_dec_lt(v___x_1311_, v___x_1310_);
if (v___x_1312_ == 0)
{
lean_dec(v___x_1311_);
v_x_1269_ = v_n_1296_;
v_x_1270_ = v_zero_1271_;
goto _start;
}
else
{
v_x_1269_ = v_n_1296_;
v_x_1270_ = v___x_1311_;
goto _start;
}
}
else
{
lean_object* v_val_1315_; lean_object* v___x_1316_; 
lean_dec(v_n_1296_);
lean_dec(v_x_1268_);
lean_inc(v___x_1306_);
v_val_1315_ = lean_noption_get(v___x_1306_);
v___x_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1316_, 0, v_x_1270_);
lean_ctor_set(v___x_1316_, 1, v_val_1308_);
lean_ctor_set(v___x_1316_, 2, v_val_1315_);
return v___x_1316_;
}
}
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_array_get_size(v_keyArray_1282_);
v___x_1300_ = lean_nat_add(v_x_1270_, v_one_1295_);
lean_dec(v_x_1270_);
v___x_1301_ = lean_nat_dec_lt(v___x_1300_, v___x_1299_);
if (v___x_1301_ == 0)
{
lean_dec(v___x_1300_);
v_x_1268_ = v___y_1298_;
v_x_1269_ = v_n_1296_;
v_x_1270_ = v_zero_1271_;
goto _start;
}
else
{
v_x_1268_ = v___y_1298_;
v_x_1269_ = v_n_1296_;
v_x_1270_ = v___x_1300_;
goto _start;
}
}
v___jp_1304_:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v___x_1305_; 
lean_inc(v_x_1270_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_x_1270_);
v___y_1298_ = v___x_1305_;
goto v___jp_1297_;
}
else
{
v___y_1298_ = v_x_1268_;
goto v___jp_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_m_1317_, lean_object* v_query_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_m_1317_, v_query_1318_, v_x_1319_, v_x_1320_, v_x_1321_);
lean_dec_ref(v_query_1318_);
lean_dec_ref(v_m_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1323_, lean_object* v_query_1324_){
_start:
{
lean_object* v_keyArray_1325_; lean_object* v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v_fold_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_keyArray_1325_ = lean_ctor_get(v_m_1323_, 1);
v___x_1326_ = lean_array_get_size(v_keyArray_1325_);
v___x_1327_ = l_Lean_Expr_hash(v_query_1324_);
v___x_1328_ = 32ULL;
v___x_1329_ = lean_uint64_shift_right(v___x_1327_, v___x_1328_);
v_fold_1330_ = lean_uint64_xor(v___x_1327_, v___x_1329_);
v___x_1331_ = 16ULL;
v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
v___x_1335_ = lean_usize_of_nat(v___x_1326_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
v___x_1339_ = lean_usize_to_nat(v___x_1338_);
v___x_1340_ = lean_box(0);
v___x_1341_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_m_1323_, v_query_1324_, v___x_1340_, v___x_1326_, v___x_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg___boxed(lean_object* v_m_1342_, lean_object* v_query_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_1342_, v_query_1343_);
lean_dec_ref(v_query_1343_);
lean_dec_ref(v_m_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_m_1345_, lean_object* v_query_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_1345_, v_query_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_index_1348_; lean_object* v_key_1349_; lean_object* v_value_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_index_1348_ = lean_ctor_get(v___x_1347_, 0);
v_key_1349_ = lean_ctor_get(v___x_1347_, 1);
v_value_1350_ = lean_ctor_get(v___x_1347_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1347_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_value_1350_);
lean_inc(v_key_1349_);
lean_inc(v_index_1348_);
lean_dec(v___x_1347_);
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
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_index_1348_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_key_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_value_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v___x_1358_; 
lean_dec(v___x_1347_);
v___x_1358_ = lean_box(1);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_m_1359_, lean_object* v_query_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_m_1359_, v_query_1360_);
lean_dec_ref(v_query_1360_);
lean_dec_ref(v_m_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_m_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_value_1365_; lean_object* v___x_1366_; 
v_value_1365_ = lean_ctor_get(v___x_1364_, 2);
lean_inc(v_value_1365_);
lean_dec_ref_known(v___x_1364_, 3);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_value_1365_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1368_, v_a_1369_);
lean_dec_ref(v_a_1369_);
lean_dec_ref(v_m_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg(lean_object* v_b_1371_, lean_object* v_acc_1372_, lean_object* v_i_1373_){
_start:
{
lean_object* v___y_1375_; lean_object* v_keyArray_1383_; lean_object* v_valueArray_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_keyArray_1383_ = lean_ctor_get(v_b_1371_, 1);
v_valueArray_1384_ = lean_ctor_get(v_b_1371_, 2);
v___x_1385_ = lean_array_get_size(v_keyArray_1383_);
v___x_1386_ = lean_nat_dec_lt(v_i_1373_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v_i_1373_);
return v_acc_1372_;
}
else
{
lean_object* v___x_1387_; uint8_t v_isSome_1388_; 
v___x_1387_ = lean_array_fget_borrowed(v_keyArray_1383_, v_i_1373_);
v_isSome_1388_ = lean_noption_is_some(v___x_1387_);
if (v_isSome_1388_ == 0)
{
goto v___jp_1379_;
}
else
{
lean_object* v___x_1389_; uint8_t v_isSome_1390_; 
v___x_1389_ = lean_array_fget_borrowed(v_valueArray_1384_, v_i_1373_);
v_isSome_1390_ = lean_noption_is_some(v___x_1389_);
if (v_isSome_1390_ == 0)
{
goto v___jp_1379_;
}
else
{
lean_object* v_val_1391_; lean_object* v_val_1392_; lean_object* v_i_1394_; lean_object* v___x_1399_; 
lean_inc(v___x_1387_);
v_val_1391_ = lean_noption_get(v___x_1387_);
lean_inc(v___x_1389_);
v_val_1392_ = lean_noption_get(v___x_1389_);
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_acc_1372_, v_val_1391_);
switch(lean_obj_tag(v___x_1399_))
{
case 0:
{
lean_object* v_index_1400_; lean_object* v_size_1401_; lean_object* v___x_1402_; 
v_index_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_index_1400_);
lean_dec_ref_known(v___x_1399_, 3);
v_size_1401_ = lean_ctor_get(v_acc_1372_, 0);
lean_inc(v_size_1401_);
v___x_1402_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1372_, v_size_1401_, v_index_1400_, v_val_1391_, v_val_1392_);
lean_dec(v_index_1400_);
v___y_1375_ = v___x_1402_;
goto v___jp_1374_;
}
case 1:
{
lean_object* v_index_1403_; 
v_index_1403_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_index_1403_);
lean_dec_ref_known(v___x_1399_, 1);
v_i_1394_ = v_index_1403_;
goto v___jp_1393_;
}
default: 
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1372_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_index_1406_; 
v_index_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_index_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_i_1394_ = v_index_1406_;
goto v___jp_1393_;
}
else
{
lean_dec(v_val_1392_);
lean_dec(v_val_1391_);
v___y_1375_ = v_acc_1372_;
goto v___jp_1374_;
}
}
}
v___jp_1393_:
{
lean_object* v_size_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_size_1395_ = lean_ctor_get(v_acc_1372_, 0);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_size_1395_, v___x_1396_);
v___x_1398_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1372_, v___x_1397_, v_i_1394_, v_val_1391_, v_val_1392_);
lean_dec(v_i_1394_);
v___y_1375_ = v___x_1398_;
goto v___jp_1374_;
}
}
}
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_i_1373_, v___x_1376_);
lean_dec(v_i_1373_);
v_acc_1372_ = v___y_1375_;
v_i_1373_ = v___x_1377_;
goto _start;
}
v___jp_1379_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v_i_1373_, v___x_1380_);
lean_dec(v_i_1373_);
v_i_1373_ = v___x_1381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg___boxed(lean_object* v_b_1407_, lean_object* v_acc_1408_, lean_object* v_i_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg(v_b_1407_, v_acc_1408_, v_i_1409_);
lean_dec_ref(v_b_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg(lean_object* v_init_1411_, lean_object* v_b_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg(v_b_1412_, v_init_1411_, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg___boxed(lean_object* v_init_1415_, lean_object* v_b_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg(v_init_1415_, v_b_1416_);
lean_dec_ref(v_b_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(lean_object* v_m_1418_){
_start:
{
lean_object* v_keyArray_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_cellCount_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v_target_1426_; lean_object* v___x_1427_; 
v_keyArray_1419_ = lean_ctor_get(v_m_1418_, 1);
v___x_1420_ = lean_array_get_size(v_keyArray_1419_);
v___x_1421_ = lean_unsigned_to_nat(2u);
v_cellCount_1422_ = lean_nat_mul(v___x_1420_, v___x_1421_);
v___x_1423_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1422_);
v___x_1424_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1422_);
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1422_);
v_target_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1426_, 0, v___x_1423_);
lean_ctor_set(v_target_1426_, 1, v___x_1424_);
lean_ctor_set(v_target_1426_, 2, v___x_1425_);
v___x_1427_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg(v_target_1426_, v_m_1418_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg___boxed(lean_object* v_m_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_m_1428_);
lean_dec_ref(v_m_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21(lean_object* v_msgData_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v_env_1437_; lean_object* v___x_1438_; lean_object* v_mctx_1439_; lean_object* v_lctx_1440_; lean_object* v_options_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1436_ = lean_st_ref_get(v___y_1434_);
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = lean_st_ref_get(v___y_1432_);
v_mctx_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_mctx_1439_);
lean_dec(v___x_1438_);
v_lctx_1440_ = lean_ctor_get(v___y_1431_, 2);
v_options_1441_ = lean_ctor_get(v___y_1433_, 2);
lean_inc_ref(v_options_1441_);
lean_inc_ref(v_lctx_1440_);
v___x_1442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1442_, 0, v_env_1437_);
lean_ctor_set(v___x_1442_, 1, v_mctx_1439_);
lean_ctor_set(v___x_1442_, 2, v_lctx_1440_);
lean_ctor_set(v___x_1442_, 3, v_options_1441_);
v___x_1443_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_msgData_1430_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21___boxed(lean_object* v_msgData_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21(v_msgData_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1451_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1452_; double v___x_1453_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_float_of_nat(v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_ref_1464_; lean_object* v___x_1465_; lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1510_; 
v_ref_1464_ = lean_ctor_get(v___y_1461_, 5);
v___x_1465_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10_spec__21(v_msg_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1510_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1510_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v_traceState_1471_; lean_object* v_env_1472_; lean_object* v_nextMacroScope_1473_; lean_object* v_ngen_1474_; lean_object* v_auxDeclNGen_1475_; lean_object* v_cache_1476_; lean_object* v_messages_1477_; lean_object* v_infoState_1478_; lean_object* v_snapshotTasks_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1509_; 
v___x_1470_ = lean_st_ref_take(v___y_1462_);
v_traceState_1471_ = lean_ctor_get(v___x_1470_, 4);
v_env_1472_ = lean_ctor_get(v___x_1470_, 0);
v_nextMacroScope_1473_ = lean_ctor_get(v___x_1470_, 1);
v_ngen_1474_ = lean_ctor_get(v___x_1470_, 2);
v_auxDeclNGen_1475_ = lean_ctor_get(v___x_1470_, 3);
v_cache_1476_ = lean_ctor_get(v___x_1470_, 5);
v_messages_1477_ = lean_ctor_get(v___x_1470_, 6);
v_infoState_1478_ = lean_ctor_get(v___x_1470_, 7);
v_snapshotTasks_1479_ = lean_ctor_get(v___x_1470_, 8);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1481_ = v___x_1470_;
v_isShared_1482_ = v_isSharedCheck_1509_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_snapshotTasks_1479_);
lean_inc(v_infoState_1478_);
lean_inc(v_messages_1477_);
lean_inc(v_cache_1476_);
lean_inc(v_traceState_1471_);
lean_inc(v_auxDeclNGen_1475_);
lean_inc(v_ngen_1474_);
lean_inc(v_nextMacroScope_1473_);
lean_inc(v_env_1472_);
lean_dec(v___x_1470_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1509_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint64_t v_tid_1483_; lean_object* v_traces_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1508_; 
v_tid_1483_ = lean_ctor_get_uint64(v_traceState_1471_, sizeof(void*)*1);
v_traces_1484_ = lean_ctor_get(v_traceState_1471_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_traceState_1471_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1486_ = v_traceState_1471_;
v_isShared_1487_ = v_isSharedCheck_1508_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_traces_1484_);
lean_dec(v_traceState_1471_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1508_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; double v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0);
v___x_1490_ = 0;
v___x_1491_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_1492_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1492_, 0, v_cls_1457_);
lean_ctor_set(v___x_1492_, 1, v___x_1488_);
lean_ctor_set(v___x_1492_, 2, v___x_1491_);
lean_ctor_set_float(v___x_1492_, sizeof(void*)*3, v___x_1489_);
lean_ctor_set_float(v___x_1492_, sizeof(void*)*3 + 8, v___x_1489_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 16, v___x_1490_);
v___x_1493_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2));
v___x_1494_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v_a_1466_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
lean_inc(v_ref_1464_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_ref_1464_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Lean_PersistentArray_push___redArg(v_traces_1484_, v___x_1495_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1496_);
v___x_1498_ = v___x_1486_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1496_);
lean_ctor_set_uint64(v_reuseFailAlloc_1507_, sizeof(void*)*1, v_tid_1483_);
v___x_1498_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v___x_1498_);
v___x_1500_ = v___x_1481_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_env_1472_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_nextMacroScope_1473_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_ngen_1474_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_auxDeclNGen_1475_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v_cache_1476_);
lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_messages_1477_);
lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_infoState_1478_);
lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_snapshotTasks_1479_);
v___x_1500_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = lean_st_ref_put(v___y_1462_, v___x_1500_);
v___x_1502_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1502_);
v___x_1504_ = v___x_1468_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_cls_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_cls_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg(lean_object* v_declName_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v_env_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1522_ = lean_st_ref_get(v___y_1520_);
v_env_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc_ref(v_env_1523_);
lean_dec(v___x_1522_);
v___x_1524_ = l_Lean_Meta_isMatcherCore(v_env_1523_, v_declName_1519_);
v___x_1525_ = lean_box(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg___boxed(lean_object* v_declName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg(v_declName_1527_, v___y_1528_);
lean_dec(v___y_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg(lean_object* v_name_1531_, lean_object* v_type_1532_, lean_object* v_val_1533_, lean_object* v_k_1534_, uint8_t v_nondep_1535_, uint8_t v_kind_1536_, uint8_t v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_box(v___y_1537_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1546_, 0, v_k_1534_);
lean_closure_set(v___f_1546_, 1, v___x_1545_);
lean_closure_set(v___f_1546_, 2, v___y_1538_);
lean_closure_set(v___f_1546_, 3, v___y_1539_);
v___x_1547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1531_, v_type_1532_, v_val_1533_, v___f_1546_, v_nondep_1535_, v_kind_1536_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1547_) == 0)
{
return v___x_1547_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg___boxed(lean_object* v_name_1556_, lean_object* v_type_1557_, lean_object* v_val_1558_, lean_object* v_k_1559_, lean_object* v_nondep_1560_, lean_object* v_kind_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_nondep_boxed_1570_; uint8_t v_kind_boxed_1571_; uint8_t v___y_71273__boxed_1572_; lean_object* v_res_1573_; 
v_nondep_boxed_1570_ = lean_unbox(v_nondep_1560_);
v_kind_boxed_1571_ = lean_unbox(v_kind_1561_);
v___y_71273__boxed_1572_ = lean_unbox(v___y_1562_);
v_res_1573_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg(v_name_1556_, v_type_1557_, v_val_1558_, v_k_1559_, v_nondep_boxed_1570_, v_kind_boxed_1571_, v___y_71273__boxed_1572_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__5(lean_object* v_msg_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = l_Lean_instInhabitedExpr;
v___x_1576_ = lean_panic_fn_borrowed(v___x_1575_, v_msg_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1579_, lean_object* v_body_1580_, lean_object* v_x_1581_, uint8_t v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_array_push(v_fvars_1579_, v_x_1581_);
v___x_1591_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1590_, v_body_1580_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1592_, lean_object* v_body_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___y_71436__boxed_1603_; lean_object* v_res_1604_; 
v___y_71436__boxed_1603_ = lean_unbox(v___y_1595_);
v_res_1604_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1592_, v_body_1593_, v_x_1594_, v___y_71436__boxed_1603_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1605_, lean_object* v_e_1606_, uint8_t v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
if (lean_obj_tag(v_e_1606_) == 6)
{
lean_object* v_binderName_1615_; lean_object* v_binderType_1616_; lean_object* v_body_1617_; uint8_t v_binderInfo_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_binderName_1615_ = lean_ctor_get(v_e_1606_, 0);
lean_inc(v_binderName_1615_);
v_binderType_1616_ = lean_ctor_get(v_e_1606_, 1);
lean_inc_ref(v_binderType_1616_);
v_body_1617_ = lean_ctor_get(v_e_1606_, 2);
lean_inc_ref(v_body_1617_);
v_binderInfo_1618_ = lean_ctor_get_uint8(v_e_1606_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1606_, 3);
v___x_1619_ = lean_expr_instantiate_rev(v_binderType_1616_, v_fvars_1605_);
lean_dec_ref(v_binderType_1616_);
v___x_1620_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1619_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___f_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___f_1622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1622_, 0, v_fvars_1605_);
lean_closure_set(v___f_1622_, 1, v_body_1617_);
v___x_1623_ = 0;
v___x_1624_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(v_binderName_1615_, v_binderInfo_1618_, v_a_1621_, v___f_1622_, v___x_1623_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1624_;
}
else
{
lean_dec_ref(v_body_1617_);
lean_dec(v_binderName_1615_);
lean_dec_ref(v_fvars_1605_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_expr_instantiate_rev(v_e_1606_, v_fvars_1605_);
lean_dec_ref(v_e_1606_);
v___x_1626_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1625_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; uint8_t v___x_1628_; uint8_t v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = 0;
v___x_1629_ = 1;
v___x_1630_ = 1;
v___x_1631_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1605_, v_a_1627_, v___x_1628_, v___x_1629_, v___x_1628_, v___x_1629_, v___x_1630_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec_ref(v_fvars_1605_);
return v___x_1631_;
}
else
{
lean_dec_ref(v_fvars_1605_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1632_, uint8_t v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
if (v_a_1633_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1642_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1641_, v_e_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1644_ = l_Lean_Meta_Sym_etaReduce(v_e_1632_);
lean_dec_ref(v_e_1632_);
v___x_1645_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1643_, v___x_1644_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1646_, lean_object* v_body_1647_, lean_object* v_x_1648_, uint8_t v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_array_push(v_fvars_1646_, v_x_1648_);
v___x_1658_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1657_, v_body_1647_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1659_, lean_object* v_body_1660_, lean_object* v_x_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v___y_71447__boxed_1670_; lean_object* v_res_1671_; 
v___y_71447__boxed_1670_ = lean_unbox(v___y_1662_);
v_res_1671_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1659_, v_body_1660_, v_x_1661_, v___y_71447__boxed_1670_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1672_, lean_object* v_e_1673_, uint8_t v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
if (lean_obj_tag(v_e_1673_) == 8)
{
lean_object* v_declName_1682_; lean_object* v_type_1683_; lean_object* v_value_1684_; lean_object* v_body_1685_; uint8_t v_nondep_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_declName_1682_ = lean_ctor_get(v_e_1673_, 0);
lean_inc(v_declName_1682_);
v_type_1683_ = lean_ctor_get(v_e_1673_, 1);
lean_inc_ref(v_type_1683_);
v_value_1684_ = lean_ctor_get(v_e_1673_, 2);
lean_inc_ref(v_value_1684_);
v_body_1685_ = lean_ctor_get(v_e_1673_, 3);
lean_inc_ref(v_body_1685_);
v_nondep_1686_ = lean_ctor_get_uint8(v_e_1673_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1673_, 4);
v___x_1687_ = lean_expr_instantiate_rev(v_type_1683_, v_fvars_1672_);
lean_dec_ref(v_type_1683_);
v___x_1688_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1687_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_expr_instantiate_rev(v_value_1684_, v_fvars_1672_);
lean_dec_ref(v_value_1684_);
v___x_1691_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1690_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___f_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___f_1693_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1693_, 0, v_fvars_1672_);
lean_closure_set(v___f_1693_, 1, v_body_1685_);
v___x_1694_ = 0;
v___x_1695_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg(v_declName_1682_, v_a_1689_, v_a_1692_, v___f_1693_, v_nondep_1686_, v___x_1694_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
return v___x_1695_;
}
else
{
lean_dec(v_a_1689_);
lean_dec_ref(v_body_1685_);
lean_dec(v_declName_1682_);
lean_dec_ref(v_fvars_1672_);
return v___x_1691_;
}
}
else
{
lean_dec_ref(v_body_1685_);
lean_dec_ref(v_value_1684_);
lean_dec(v_declName_1682_);
lean_dec_ref(v_fvars_1672_);
return v___x_1688_;
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_expr_instantiate_rev(v_e_1673_, v_fvars_1672_);
lean_dec_ref(v_e_1673_);
v___x_1697_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1696_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; uint8_t v___x_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = 1;
v___x_1700_ = 0;
v___x_1701_ = 1;
v___x_1702_ = l_Lean_Meta_mkLetFVars(v_fvars_1672_, v_a_1698_, v___x_1699_, v___x_1700_, v___x_1701_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec_ref(v_fvars_1672_);
return v___x_1702_;
}
else
{
lean_dec_ref(v_fvars_1672_);
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1703_, uint8_t v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
if (v_a_1704_ == 0)
{
uint8_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = 1;
v___x_1713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1703_, v___x_1712_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1715_, uint8_t v_report_1716_, uint8_t v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; 
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc_ref(v_e_1715_);
v___x_1725_ = lean_infer_type(v_e_1715_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_Meta_isProp(v_a_1726_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1740_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1740_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1740_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
if (v_a_1717_ == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_unbox(v_a_1728_);
lean_dec(v_a_1728_);
if (v___x_1736_ == 0)
{
lean_del_object(v___x_1730_);
goto v___jp_1732_;
}
else
{
lean_object* v___x_1738_; 
lean_dec(v_a_1726_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_e_1715_);
v___x_1738_ = v___x_1730_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_e_1715_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_del_object(v___x_1730_);
lean_dec(v_a_1728_);
goto v___jp_1732_;
}
v___jp_1732_:
{
lean_object* v___x_1733_; 
v___x_1733_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1726_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1715_, v_a_1734_, v_report_1716_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1735_;
}
else
{
lean_dec_ref(v_e_1715_);
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1726_);
lean_dec_ref(v_e_1715_);
v_a_1741_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1727_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1727_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_dec_ref(v_e_1715_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1749_, uint8_t v_report_1750_, uint8_t v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
if (v_a_1751_ == 0)
{
lean_object* v___x_1759_; lean_object* v_canon_1760_; lean_object* v_cache_1761_; lean_object* v___x_1762_; 
v___x_1759_ = lean_st_ref_get(v_a_1753_);
v_canon_1760_ = lean_ctor_get(v___x_1759_, 9);
lean_inc_ref(v_canon_1760_);
lean_dec(v___x_1759_);
v_cache_1761_ = lean_ctor_get(v_canon_1760_, 0);
lean_inc_ref(v_cache_1761_);
lean_dec_ref(v_canon_1760_);
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1761_, v_e_1749_);
lean_dec_ref(v_cache_1761_);
if (lean_obj_tag(v___x_1762_) == 1)
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_e_1749_);
v_val_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 0);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_val_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___x_1762_);
lean_inc_ref(v_e_1749_);
v___x_1771_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1749_, v_report_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1875_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1875_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1875_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v_canon_1777_; lean_object* v_share_1778_; lean_object* v_maxFVar_1779_; lean_object* v_proofInstInfo_1780_; lean_object* v_inferType_1781_; lean_object* v_getLevel_1782_; lean_object* v_congrInfo_1783_; lean_object* v_defEqI_1784_; lean_object* v_extensions_1785_; lean_object* v_issues_1786_; lean_object* v_instanceOverrides_1787_; uint8_t v_debug_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1874_; 
v___x_1776_ = lean_st_ref_take(v_a_1753_);
v_canon_1777_ = lean_ctor_get(v___x_1776_, 9);
v_share_1778_ = lean_ctor_get(v___x_1776_, 0);
v_maxFVar_1779_ = lean_ctor_get(v___x_1776_, 1);
v_proofInstInfo_1780_ = lean_ctor_get(v___x_1776_, 2);
v_inferType_1781_ = lean_ctor_get(v___x_1776_, 3);
v_getLevel_1782_ = lean_ctor_get(v___x_1776_, 4);
v_congrInfo_1783_ = lean_ctor_get(v___x_1776_, 5);
v_defEqI_1784_ = lean_ctor_get(v___x_1776_, 6);
v_extensions_1785_ = lean_ctor_get(v___x_1776_, 7);
v_issues_1786_ = lean_ctor_get(v___x_1776_, 8);
v_instanceOverrides_1787_ = lean_ctor_get(v___x_1776_, 10);
v_debug_1788_ = lean_ctor_get_uint8(v___x_1776_, sizeof(void*)*11);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1790_ = v___x_1776_;
v_isShared_1791_ = v_isSharedCheck_1874_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_instanceOverrides_1787_);
lean_inc(v_canon_1777_);
lean_inc(v_issues_1786_);
lean_inc(v_extensions_1785_);
lean_inc(v_defEqI_1784_);
lean_inc(v_congrInfo_1783_);
lean_inc(v_getLevel_1782_);
lean_inc(v_inferType_1781_);
lean_inc(v_proofInstInfo_1780_);
lean_inc(v_maxFVar_1779_);
lean_inc(v_share_1778_);
lean_dec(v___x_1776_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1874_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_cache_1792_; lean_object* v_cacheInType_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1873_; 
v_cache_1792_ = lean_ctor_get(v_canon_1777_, 0);
v_cacheInType_1793_ = lean_ctor_get(v_canon_1777_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_canon_1777_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1795_ = v_canon_1777_;
v_isShared_1796_ = v_isSharedCheck_1873_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_cacheInType_1793_);
lean_inc(v_cache_1792_);
lean_dec(v_canon_1777_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1873_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___y_1798_; lean_object* v___y_1810_; lean_object* v_i_1811_; lean_object* v___y_1817_; lean_object* v___y_1827_; lean_object* v_i_1828_; lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1792_, v_e_1749_);
switch(lean_obj_tag(v___x_1843_))
{
case 0:
{
lean_object* v_index_1844_; lean_object* v_size_1845_; lean_object* v___x_1846_; 
v_index_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_index_1844_);
lean_dec_ref_known(v___x_1843_, 3);
v_size_1845_ = lean_ctor_get(v_cache_1792_, 0);
lean_inc(v_size_1845_);
lean_inc(v_a_1772_);
v___x_1846_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_1792_, v_size_1845_, v_index_1844_, v_e_1749_, v_a_1772_);
lean_dec(v_index_1844_);
v___y_1798_ = v___x_1846_;
goto v___jp_1797_;
}
case 1:
{
lean_object* v_index_1847_; lean_object* v_size_1848_; lean_object* v_keyArray_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_index_1847_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_index_1847_);
lean_dec_ref_known(v___x_1843_, 1);
v_size_1848_ = lean_ctor_get(v_cache_1792_, 0);
v_keyArray_1849_ = lean_ctor_get(v_cache_1792_, 1);
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = lean_nat_add(v_size_1848_, v___x_1850_);
v___x_1852_ = lean_array_get_size(v_keyArray_1849_);
v___x_1853_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v___x_1851_);
lean_dec(v_index_1847_);
goto v___jp_1833_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1854_ = lean_unsigned_to_nat(4u);
v___x_1855_ = lean_nat_mul(v___x_1851_, v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(3u);
v___x_1857_ = lean_nat_mul(v___x_1852_, v___x_1856_);
v___x_1858_ = lean_nat_dec_le(v___x_1855_, v___x_1857_);
lean_dec(v___x_1857_);
lean_dec(v___x_1855_);
if (v___x_1858_ == 0)
{
lean_dec(v___x_1851_);
lean_dec(v_index_1847_);
goto v___jp_1833_;
}
else
{
lean_object* v___x_1859_; 
lean_inc(v_a_1772_);
v___x_1859_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_1792_, v___x_1851_, v_index_1847_, v_e_1749_, v_a_1772_);
lean_dec(v_index_1847_);
v___y_1798_ = v___x_1859_;
goto v___jp_1797_;
}
}
}
default: 
{
lean_object* v_size_1860_; lean_object* v_keyArray_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_size_1860_ = lean_ctor_get(v_cache_1792_, 0);
v_keyArray_1861_ = lean_ctor_get(v_cache_1792_, 1);
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_add(v_size_1860_, v___x_1862_);
v___x_1864_ = lean_array_get_size(v_keyArray_1861_);
v___x_1865_ = lean_nat_dec_lt(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec(v___x_1863_);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_1792_);
lean_dec_ref(v_cache_1792_);
v___y_1817_ = v___x_1866_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1867_ = lean_unsigned_to_nat(4u);
v___x_1868_ = lean_nat_mul(v___x_1863_, v___x_1867_);
lean_dec(v___x_1863_);
v___x_1869_ = lean_unsigned_to_nat(3u);
v___x_1870_ = lean_nat_mul(v___x_1864_, v___x_1869_);
v___x_1871_ = lean_nat_dec_le(v___x_1868_, v___x_1870_);
lean_dec(v___x_1870_);
lean_dec(v___x_1868_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_1792_);
lean_dec_ref(v_cache_1792_);
v___y_1817_ = v___x_1872_;
goto v___jp_1816_;
}
else
{
v___y_1817_ = v_cache_1792_;
goto v___jp_1816_;
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___y_1798_);
v___x_1800_ = v___x_1795_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___y_1798_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_cacheInType_1793_);
v___x_1800_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 9, v___x_1800_);
v___x_1802_ = v___x_1790_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_share_1778_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_maxFVar_1779_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_proofInstInfo_1780_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_inferType_1781_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_getLevel_1782_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_congrInfo_1783_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_defEqI_1784_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_extensions_1785_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_issues_1786_);
lean_ctor_set(v_reuseFailAlloc_1807_, 9, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1807_, 10, v_instanceOverrides_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*11, v_debug_1788_);
v___x_1802_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_st_ref_put(v_a_1753_, v___x_1802_);
if (v_isShared_1775_ == 0)
{
v___x_1805_ = v___x_1774_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1772_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
v___jp_1809_:
{
lean_object* v_size_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_size_1812_ = lean_ctor_get(v___y_1810_, 0);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v_size_1812_, v___x_1813_);
lean_inc(v_a_1772_);
v___x_1815_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1810_, v___x_1814_, v_i_1811_, v_e_1749_, v_a_1772_);
lean_dec(v_i_1811_);
v___y_1798_ = v___x_1815_;
goto v___jp_1797_;
}
v___jp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_1817_, v_e_1749_);
switch(lean_obj_tag(v___x_1818_))
{
case 0:
{
lean_object* v_index_1819_; lean_object* v_size_1820_; lean_object* v___x_1821_; 
v_index_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_index_1819_);
lean_dec_ref_known(v___x_1818_, 3);
v_size_1820_ = lean_ctor_get(v___y_1817_, 0);
lean_inc(v_size_1820_);
lean_inc(v_a_1772_);
v___x_1821_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1817_, v_size_1820_, v_index_1819_, v_e_1749_, v_a_1772_);
lean_dec(v_index_1819_);
v___y_1798_ = v___x_1821_;
goto v___jp_1797_;
}
case 1:
{
lean_object* v_index_1822_; 
v_index_1822_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_index_1822_);
lean_dec_ref_known(v___x_1818_, 1);
v___y_1810_ = v___y_1817_;
v_i_1811_ = v_index_1822_;
goto v___jp_1809_;
}
default: 
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1817_, v___x_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_index_1825_; 
v_index_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_index_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___y_1810_ = v___y_1817_;
v_i_1811_ = v_index_1825_;
goto v___jp_1809_;
}
else
{
lean_dec_ref(v_e_1749_);
v___y_1798_ = v___y_1817_;
goto v___jp_1797_;
}
}
}
}
v___jp_1826_:
{
lean_object* v_size_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_size_1829_ = lean_ctor_get(v___y_1827_, 0);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_nat_add(v_size_1829_, v___x_1830_);
lean_inc(v_a_1772_);
v___x_1832_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1827_, v___x_1831_, v_i_1828_, v_e_1749_, v_a_1772_);
lean_dec(v_i_1828_);
v___y_1798_ = v___x_1832_;
goto v___jp_1797_;
}
v___jp_1833_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_1792_);
lean_dec_ref(v_cache_1792_);
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_1834_, v_e_1749_);
switch(lean_obj_tag(v___x_1835_))
{
case 0:
{
lean_object* v_index_1836_; lean_object* v_size_1837_; lean_object* v___x_1838_; 
v_index_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_index_1836_);
lean_dec_ref_known(v___x_1835_, 3);
v_size_1837_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_size_1837_);
lean_inc(v_a_1772_);
v___x_1838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1834_, v_size_1837_, v_index_1836_, v_e_1749_, v_a_1772_);
lean_dec(v_index_1836_);
v___y_1798_ = v___x_1838_;
goto v___jp_1797_;
}
case 1:
{
lean_object* v_index_1839_; 
v_index_1839_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_index_1839_);
lean_dec_ref_known(v___x_1835_, 1);
v___y_1827_ = v___x_1834_;
v_i_1828_ = v_index_1839_;
goto v___jp_1826_;
}
default: 
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1834_, v___x_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_index_1842_; 
v_index_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_index_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___y_1827_ = v___x_1834_;
v_i_1828_ = v_index_1842_;
goto v___jp_1826_;
}
else
{
lean_dec_ref(v_e_1749_);
v___y_1798_ = v___x_1834_;
goto v___jp_1797_;
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
lean_dec_ref(v_e_1749_);
return v___x_1771_;
}
}
}
else
{
lean_object* v___x_1876_; lean_object* v_canon_1877_; lean_object* v_cacheInType_1878_; lean_object* v___x_1879_; 
v___x_1876_ = lean_st_ref_get(v_a_1753_);
v_canon_1877_ = lean_ctor_get(v___x_1876_, 9);
lean_inc_ref(v_canon_1877_);
lean_dec(v___x_1876_);
v_cacheInType_1878_ = lean_ctor_get(v_canon_1877_, 1);
lean_inc_ref(v_cacheInType_1878_);
lean_dec_ref(v_canon_1877_);
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1878_, v_e_1749_);
lean_dec_ref(v_cacheInType_1878_);
if (lean_obj_tag(v___x_1879_) == 1)
{
lean_object* v_val_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_e_1749_);
v_val_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_val_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_val_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
lean_object* v___x_1888_; 
lean_dec(v___x_1879_);
lean_inc_ref(v_e_1749_);
v___x_1888_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1749_, v_report_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1992_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1992_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1992_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_canon_1894_; lean_object* v_share_1895_; lean_object* v_maxFVar_1896_; lean_object* v_proofInstInfo_1897_; lean_object* v_inferType_1898_; lean_object* v_getLevel_1899_; lean_object* v_congrInfo_1900_; lean_object* v_defEqI_1901_; lean_object* v_extensions_1902_; lean_object* v_issues_1903_; lean_object* v_instanceOverrides_1904_; uint8_t v_debug_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1991_; 
v___x_1893_ = lean_st_ref_take(v_a_1753_);
v_canon_1894_ = lean_ctor_get(v___x_1893_, 9);
v_share_1895_ = lean_ctor_get(v___x_1893_, 0);
v_maxFVar_1896_ = lean_ctor_get(v___x_1893_, 1);
v_proofInstInfo_1897_ = lean_ctor_get(v___x_1893_, 2);
v_inferType_1898_ = lean_ctor_get(v___x_1893_, 3);
v_getLevel_1899_ = lean_ctor_get(v___x_1893_, 4);
v_congrInfo_1900_ = lean_ctor_get(v___x_1893_, 5);
v_defEqI_1901_ = lean_ctor_get(v___x_1893_, 6);
v_extensions_1902_ = lean_ctor_get(v___x_1893_, 7);
v_issues_1903_ = lean_ctor_get(v___x_1893_, 8);
v_instanceOverrides_1904_ = lean_ctor_get(v___x_1893_, 10);
v_debug_1905_ = lean_ctor_get_uint8(v___x_1893_, sizeof(void*)*11);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1907_ = v___x_1893_;
v_isShared_1908_ = v_isSharedCheck_1991_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_instanceOverrides_1904_);
lean_inc(v_canon_1894_);
lean_inc(v_issues_1903_);
lean_inc(v_extensions_1902_);
lean_inc(v_defEqI_1901_);
lean_inc(v_congrInfo_1900_);
lean_inc(v_getLevel_1899_);
lean_inc(v_inferType_1898_);
lean_inc(v_proofInstInfo_1897_);
lean_inc(v_maxFVar_1896_);
lean_inc(v_share_1895_);
lean_dec(v___x_1893_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1991_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_cache_1909_; lean_object* v_cacheInType_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1990_; 
v_cache_1909_ = lean_ctor_get(v_canon_1894_, 0);
v_cacheInType_1910_ = lean_ctor_get(v_canon_1894_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_canon_1894_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1912_ = v_canon_1894_;
v_isShared_1913_ = v_isSharedCheck_1990_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_cacheInType_1910_);
lean_inc(v_cache_1909_);
lean_dec(v_canon_1894_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1990_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___y_1915_; lean_object* v___y_1927_; lean_object* v_i_1928_; lean_object* v___y_1944_; lean_object* v_i_1945_; lean_object* v___y_1951_; lean_object* v___x_1960_; 
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1910_, v_e_1749_);
switch(lean_obj_tag(v___x_1960_))
{
case 0:
{
lean_object* v_index_1961_; lean_object* v_size_1962_; lean_object* v___x_1963_; 
v_index_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_index_1961_);
lean_dec_ref_known(v___x_1960_, 3);
v_size_1962_ = lean_ctor_get(v_cacheInType_1910_, 0);
lean_inc(v_size_1962_);
lean_inc(v_a_1889_);
v___x_1963_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_1910_, v_size_1962_, v_index_1961_, v_e_1749_, v_a_1889_);
lean_dec(v_index_1961_);
v___y_1915_ = v___x_1963_;
goto v___jp_1914_;
}
case 1:
{
lean_object* v_index_1964_; lean_object* v_size_1965_; lean_object* v_keyArray_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_index_1964_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_index_1964_);
lean_dec_ref_known(v___x_1960_, 1);
v_size_1965_ = lean_ctor_get(v_cacheInType_1910_, 0);
v_keyArray_1966_ = lean_ctor_get(v_cacheInType_1910_, 1);
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_nat_add(v_size_1965_, v___x_1967_);
v___x_1969_ = lean_array_get_size(v_keyArray_1966_);
v___x_1970_ = lean_nat_dec_lt(v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_dec(v___x_1968_);
lean_dec(v_index_1964_);
goto v___jp_1933_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1971_ = lean_unsigned_to_nat(4u);
v___x_1972_ = lean_nat_mul(v___x_1968_, v___x_1971_);
v___x_1973_ = lean_unsigned_to_nat(3u);
v___x_1974_ = lean_nat_mul(v___x_1969_, v___x_1973_);
v___x_1975_ = lean_nat_dec_le(v___x_1972_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1972_);
if (v___x_1975_ == 0)
{
lean_dec(v___x_1968_);
lean_dec(v_index_1964_);
goto v___jp_1933_;
}
else
{
lean_object* v___x_1976_; 
lean_inc(v_a_1889_);
v___x_1976_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_1910_, v___x_1968_, v_index_1964_, v_e_1749_, v_a_1889_);
lean_dec(v_index_1964_);
v___y_1915_ = v___x_1976_;
goto v___jp_1914_;
}
}
}
default: 
{
lean_object* v_size_1977_; lean_object* v_keyArray_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_size_1977_ = lean_ctor_get(v_cacheInType_1910_, 0);
v_keyArray_1978_ = lean_ctor_get(v_cacheInType_1910_, 1);
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_size_1977_, v___x_1979_);
v___x_1981_ = lean_array_get_size(v_keyArray_1978_);
v___x_1982_ = lean_nat_dec_lt(v___x_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec(v___x_1980_);
v___x_1983_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_1910_);
lean_dec_ref(v_cacheInType_1910_);
v___y_1951_ = v___x_1983_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1984_ = lean_unsigned_to_nat(4u);
v___x_1985_ = lean_nat_mul(v___x_1980_, v___x_1984_);
lean_dec(v___x_1980_);
v___x_1986_ = lean_unsigned_to_nat(3u);
v___x_1987_ = lean_nat_mul(v___x_1981_, v___x_1986_);
v___x_1988_ = lean_nat_dec_le(v___x_1985_, v___x_1987_);
lean_dec(v___x_1987_);
lean_dec(v___x_1985_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_1910_);
lean_dec_ref(v_cacheInType_1910_);
v___y_1951_ = v___x_1989_;
goto v___jp_1950_;
}
else
{
v___y_1951_ = v_cacheInType_1910_;
goto v___jp_1950_;
}
}
}
}
v___jp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v___y_1915_);
v___x_1917_ = v___x_1912_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_cache_1909_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___y_1915_);
v___x_1917_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1919_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 9, v___x_1917_);
v___x_1919_ = v___x_1907_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_share_1895_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_maxFVar_1896_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_proofInstInfo_1897_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_inferType_1898_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_getLevel_1899_);
lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_congrInfo_1900_);
lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_defEqI_1901_);
lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_extensions_1902_);
lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_issues_1903_);
lean_ctor_set(v_reuseFailAlloc_1924_, 9, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1924_, 10, v_instanceOverrides_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*11, v_debug_1905_);
v___x_1919_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_st_ref_put(v_a_1753_, v___x_1919_);
if (v_isShared_1892_ == 0)
{
v___x_1922_ = v___x_1891_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1889_);
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
v___jp_1926_:
{
lean_object* v_size_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_size_1929_ = lean_ctor_get(v___y_1927_, 0);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_add(v_size_1929_, v___x_1930_);
lean_inc(v_a_1889_);
v___x_1932_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1927_, v___x_1931_, v_i_1928_, v_e_1749_, v_a_1889_);
lean_dec(v_i_1928_);
v___y_1915_ = v___x_1932_;
goto v___jp_1914_;
}
v___jp_1933_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_1910_);
lean_dec_ref(v_cacheInType_1910_);
v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_1934_, v_e_1749_);
switch(lean_obj_tag(v___x_1935_))
{
case 0:
{
lean_object* v_index_1936_; lean_object* v_size_1937_; lean_object* v___x_1938_; 
v_index_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_index_1936_);
lean_dec_ref_known(v___x_1935_, 3);
v_size_1937_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_size_1937_);
lean_inc(v_a_1889_);
v___x_1938_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1934_, v_size_1937_, v_index_1936_, v_e_1749_, v_a_1889_);
lean_dec(v_index_1936_);
v___y_1915_ = v___x_1938_;
goto v___jp_1914_;
}
case 1:
{
lean_object* v_index_1939_; 
v_index_1939_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_index_1939_);
lean_dec_ref_known(v___x_1935_, 1);
v___y_1927_ = v___x_1934_;
v_i_1928_ = v_index_1939_;
goto v___jp_1926_;
}
default: 
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1934_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_index_1942_; 
v_index_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_index_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___y_1927_ = v___x_1934_;
v_i_1928_ = v_index_1942_;
goto v___jp_1926_;
}
else
{
lean_dec_ref(v_e_1749_);
v___y_1915_ = v___x_1934_;
goto v___jp_1914_;
}
}
}
}
v___jp_1943_:
{
lean_object* v_size_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_size_1946_ = lean_ctor_get(v___y_1944_, 0);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_size_1946_, v___x_1947_);
lean_inc(v_a_1889_);
v___x_1949_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1944_, v___x_1948_, v_i_1945_, v_e_1749_, v_a_1889_);
lean_dec(v_i_1945_);
v___y_1915_ = v___x_1949_;
goto v___jp_1914_;
}
v___jp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_1951_, v_e_1749_);
switch(lean_obj_tag(v___x_1952_))
{
case 0:
{
lean_object* v_index_1953_; lean_object* v_size_1954_; lean_object* v___x_1955_; 
v_index_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_index_1953_);
lean_dec_ref_known(v___x_1952_, 3);
v_size_1954_ = lean_ctor_get(v___y_1951_, 0);
lean_inc(v_size_1954_);
lean_inc(v_a_1889_);
v___x_1955_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1951_, v_size_1954_, v_index_1953_, v_e_1749_, v_a_1889_);
lean_dec(v_index_1953_);
v___y_1915_ = v___x_1955_;
goto v___jp_1914_;
}
case 1:
{
lean_object* v_index_1956_; 
v_index_1956_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_index_1956_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1944_ = v___y_1951_;
v_i_1945_ = v_index_1956_;
goto v___jp_1943_;
}
default: 
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1951_, v___x_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_index_1959_; 
v_index_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_index_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1944_ = v___y_1951_;
v_i_1945_ = v_index_1959_;
goto v___jp_1943_;
}
else
{
lean_dec_ref(v_e_1749_);
v___y_1915_ = v___y_1951_;
goto v___jp_1914_;
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
lean_dec_ref(v_e_1749_);
return v___x_1888_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_2009_ = l_Lean_mkConst(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_2010_, lean_object* v_prop_2011_, lean_object* v_inst_2012_, lean_object* v_e_2013_, uint8_t v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
lean_inc_ref(v_prop_2011_);
v___x_2022_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2011_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2062_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2062_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2062_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_2023_);
v___x_2038_ = l_Lean_Expr_app___override(v___x_2037_, v_a_2023_);
if (v_a_2014_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2038_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___y_2042_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_a_2040_) == 0)
{
lean_inc_ref(v_inst_2012_);
v___y_2042_ = v_inst_2012_;
goto v___jp_2041_;
}
else
{
lean_object* v_val_2051_; 
v_val_2051_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v_a_2040_, 1);
v___y_2042_ = v_val_2051_;
goto v___jp_2041_;
}
v___jp_2041_:
{
lean_object* v___x_2043_; 
lean_inc_ref(v_inst_2012_);
v___x_2043_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_2012_, v___y_2042_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; size_t v___x_2045_; size_t v___x_2046_; uint8_t v___x_2047_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_ptr_addr(v_prop_2011_);
lean_dec_ref(v_prop_2011_);
v___x_2046_ = lean_ptr_addr(v_a_2023_);
v___x_2047_ = lean_usize_dec_eq(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v_inst_2012_);
v___y_2028_ = v_a_2044_;
v___y_2029_ = v___x_2047_;
goto v___jp_2027_;
}
else
{
size_t v___x_2048_; size_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2048_ = lean_ptr_addr(v_inst_2012_);
lean_dec_ref(v_inst_2012_);
v___x_2049_ = lean_ptr_addr(v_a_2044_);
v___x_2050_ = lean_usize_dec_eq(v___x_2048_, v___x_2049_);
v___y_2028_ = v_a_2044_;
v___y_2029_ = v___x_2050_;
goto v___jp_2027_;
}
}
else
{
lean_del_object(v___x_2025_);
lean_dec(v_a_2023_);
lean_dec_ref(v_e_2013_);
lean_dec_ref(v_inst_2012_);
lean_dec_ref(v_prop_2011_);
lean_dec_ref(v_g_2010_);
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_del_object(v___x_2025_);
lean_dec(v_a_2023_);
lean_dec_ref(v_e_2013_);
lean_dec_ref(v_inst_2012_);
lean_dec_ref(v_prop_2011_);
lean_dec_ref(v_g_2010_);
v_a_2052_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2039_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2039_);
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
else
{
uint8_t v___x_2060_; lean_object* v___x_2061_; 
lean_del_object(v___x_2025_);
lean_dec(v_a_2023_);
lean_dec_ref(v_e_2013_);
lean_dec_ref(v_prop_2011_);
lean_dec_ref(v_g_2010_);
v___x_2060_ = 0;
v___x_2061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_2012_, v___x_2038_, v___x_2060_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2061_;
}
v___jp_2027_:
{
if (v___y_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec_ref(v_e_2013_);
v___x_2030_ = l_Lean_mkAppB(v_g_2010_, v_a_2023_, v___y_2028_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2030_);
v___x_2032_ = v___x_2025_;
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
else
{
lean_object* v___x_2035_; 
lean_dec_ref(v___y_2028_);
lean_dec(v_a_2023_);
lean_dec_ref(v_g_2010_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v_e_2013_);
v___x_2035_ = v___x_2025_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_e_2013_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2013_);
lean_dec_ref(v_inst_2012_);
lean_dec_ref(v_prop_2011_);
lean_dec_ref(v_g_2010_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2063_, lean_object* v_prop_2064_, lean_object* v_h_2065_, lean_object* v_e_2066_, uint8_t v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
if (v_a_2067_ == 0)
{
lean_object* v___x_2075_; lean_object* v_canon_2076_; lean_object* v_cache_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_st_ref_get(v_a_2069_);
v_canon_2076_ = lean_ctor_get(v___x_2075_, 9);
lean_inc_ref(v_canon_2076_);
lean_dec(v___x_2075_);
v_cache_2077_ = lean_ctor_get(v_canon_2076_, 0);
lean_inc_ref(v_cache_2077_);
lean_dec_ref(v_canon_2076_);
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2077_, v_e_2066_);
lean_dec_ref(v_cache_2077_);
if (lean_obj_tag(v___x_2078_) == 1)
{
lean_object* v_val_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_e_2066_);
lean_dec_ref(v_h_2065_);
lean_dec_ref(v_prop_2064_);
lean_dec_ref(v_g_2063_);
v_val_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_val_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 0);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_val_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
lean_object* v___x_2087_; 
lean_dec(v___x_2078_);
lean_inc_ref(v_e_2066_);
v___x_2087_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2063_, v_prop_2064_, v_h_2065_, v_e_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2191_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2191_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2191_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v_canon_2093_; lean_object* v_share_2094_; lean_object* v_maxFVar_2095_; lean_object* v_proofInstInfo_2096_; lean_object* v_inferType_2097_; lean_object* v_getLevel_2098_; lean_object* v_congrInfo_2099_; lean_object* v_defEqI_2100_; lean_object* v_extensions_2101_; lean_object* v_issues_2102_; lean_object* v_instanceOverrides_2103_; uint8_t v_debug_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2190_; 
v___x_2092_ = lean_st_ref_take(v_a_2069_);
v_canon_2093_ = lean_ctor_get(v___x_2092_, 9);
v_share_2094_ = lean_ctor_get(v___x_2092_, 0);
v_maxFVar_2095_ = lean_ctor_get(v___x_2092_, 1);
v_proofInstInfo_2096_ = lean_ctor_get(v___x_2092_, 2);
v_inferType_2097_ = lean_ctor_get(v___x_2092_, 3);
v_getLevel_2098_ = lean_ctor_get(v___x_2092_, 4);
v_congrInfo_2099_ = lean_ctor_get(v___x_2092_, 5);
v_defEqI_2100_ = lean_ctor_get(v___x_2092_, 6);
v_extensions_2101_ = lean_ctor_get(v___x_2092_, 7);
v_issues_2102_ = lean_ctor_get(v___x_2092_, 8);
v_instanceOverrides_2103_ = lean_ctor_get(v___x_2092_, 10);
v_debug_2104_ = lean_ctor_get_uint8(v___x_2092_, sizeof(void*)*11);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2106_ = v___x_2092_;
v_isShared_2107_ = v_isSharedCheck_2190_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_instanceOverrides_2103_);
lean_inc(v_canon_2093_);
lean_inc(v_issues_2102_);
lean_inc(v_extensions_2101_);
lean_inc(v_defEqI_2100_);
lean_inc(v_congrInfo_2099_);
lean_inc(v_getLevel_2098_);
lean_inc(v_inferType_2097_);
lean_inc(v_proofInstInfo_2096_);
lean_inc(v_maxFVar_2095_);
lean_inc(v_share_2094_);
lean_dec(v___x_2092_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2190_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_cache_2108_; lean_object* v_cacheInType_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2189_; 
v_cache_2108_ = lean_ctor_get(v_canon_2093_, 0);
v_cacheInType_2109_ = lean_ctor_get(v_canon_2093_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_canon_2093_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2111_ = v_canon_2093_;
v_isShared_2112_ = v_isSharedCheck_2189_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_cacheInType_2109_);
lean_inc(v_cache_2108_);
lean_dec(v_canon_2093_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2189_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___y_2114_; lean_object* v___y_2126_; lean_object* v_i_2127_; lean_object* v___y_2133_; lean_object* v___y_2143_; lean_object* v_i_2144_; lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2108_, v_e_2066_);
switch(lean_obj_tag(v___x_2159_))
{
case 0:
{
lean_object* v_index_2160_; lean_object* v_size_2161_; lean_object* v___x_2162_; 
v_index_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_index_2160_);
lean_dec_ref_known(v___x_2159_, 3);
v_size_2161_ = lean_ctor_get(v_cache_2108_, 0);
lean_inc(v_size_2161_);
lean_inc(v_a_2088_);
v___x_2162_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2108_, v_size_2161_, v_index_2160_, v_e_2066_, v_a_2088_);
lean_dec(v_index_2160_);
v___y_2114_ = v___x_2162_;
goto v___jp_2113_;
}
case 1:
{
lean_object* v_index_2163_; lean_object* v_size_2164_; lean_object* v_keyArray_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v_index_2163_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_index_2163_);
lean_dec_ref_known(v___x_2159_, 1);
v_size_2164_ = lean_ctor_get(v_cache_2108_, 0);
v_keyArray_2165_ = lean_ctor_get(v_cache_2108_, 1);
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_size_2164_, v___x_2166_);
v___x_2168_ = lean_array_get_size(v_keyArray_2165_);
v___x_2169_ = lean_nat_dec_lt(v___x_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_dec(v___x_2167_);
lean_dec(v_index_2163_);
goto v___jp_2149_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2170_ = lean_unsigned_to_nat(4u);
v___x_2171_ = lean_nat_mul(v___x_2167_, v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(3u);
v___x_2173_ = lean_nat_mul(v___x_2168_, v___x_2172_);
v___x_2174_ = lean_nat_dec_le(v___x_2171_, v___x_2173_);
lean_dec(v___x_2173_);
lean_dec(v___x_2171_);
if (v___x_2174_ == 0)
{
lean_dec(v___x_2167_);
lean_dec(v_index_2163_);
goto v___jp_2149_;
}
else
{
lean_object* v___x_2175_; 
lean_inc(v_a_2088_);
v___x_2175_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2108_, v___x_2167_, v_index_2163_, v_e_2066_, v_a_2088_);
lean_dec(v_index_2163_);
v___y_2114_ = v___x_2175_;
goto v___jp_2113_;
}
}
}
default: 
{
lean_object* v_size_2176_; lean_object* v_keyArray_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_size_2176_ = lean_ctor_get(v_cache_2108_, 0);
v_keyArray_2177_ = lean_ctor_get(v_cache_2108_, 1);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_size_2176_, v___x_2178_);
v___x_2180_ = lean_array_get_size(v_keyArray_2177_);
v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec(v___x_2179_);
v___x_2182_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_2108_);
lean_dec_ref(v_cache_2108_);
v___y_2133_ = v___x_2182_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2183_ = lean_unsigned_to_nat(4u);
v___x_2184_ = lean_nat_mul(v___x_2179_, v___x_2183_);
lean_dec(v___x_2179_);
v___x_2185_ = lean_unsigned_to_nat(3u);
v___x_2186_ = lean_nat_mul(v___x_2180_, v___x_2185_);
v___x_2187_ = lean_nat_dec_le(v___x_2184_, v___x_2186_);
lean_dec(v___x_2186_);
lean_dec(v___x_2184_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_2108_);
lean_dec_ref(v_cache_2108_);
v___y_2133_ = v___x_2188_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v_cache_2108_;
goto v___jp_2132_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___y_2114_);
v___x_2116_ = v___x_2111_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___y_2114_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_cacheInType_2109_);
v___x_2116_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 9, v___x_2116_);
v___x_2118_ = v___x_2106_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_share_2094_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_maxFVar_2095_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_proofInstInfo_2096_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_inferType_2097_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_getLevel_2098_);
lean_ctor_set(v_reuseFailAlloc_2123_, 5, v_congrInfo_2099_);
lean_ctor_set(v_reuseFailAlloc_2123_, 6, v_defEqI_2100_);
lean_ctor_set(v_reuseFailAlloc_2123_, 7, v_extensions_2101_);
lean_ctor_set(v_reuseFailAlloc_2123_, 8, v_issues_2102_);
lean_ctor_set(v_reuseFailAlloc_2123_, 9, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 10, v_instanceOverrides_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*11, v_debug_2104_);
v___x_2118_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_st_ref_put(v_a_2069_, v___x_2118_);
if (v_isShared_2091_ == 0)
{
v___x_2121_ = v___x_2090_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2088_);
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
v___jp_2125_:
{
lean_object* v_size_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_size_2128_ = lean_ctor_get(v___y_2126_, 0);
v___x_2129_ = lean_unsigned_to_nat(1u);
v___x_2130_ = lean_nat_add(v_size_2128_, v___x_2129_);
lean_inc(v_a_2088_);
v___x_2131_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2126_, v___x_2130_, v_i_2127_, v_e_2066_, v_a_2088_);
lean_dec(v_i_2127_);
v___y_2114_ = v___x_2131_;
goto v___jp_2113_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_2133_, v_e_2066_);
switch(lean_obj_tag(v___x_2134_))
{
case 0:
{
lean_object* v_index_2135_; lean_object* v_size_2136_; lean_object* v___x_2137_; 
v_index_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_index_2135_);
lean_dec_ref_known(v___x_2134_, 3);
v_size_2136_ = lean_ctor_get(v___y_2133_, 0);
lean_inc(v_size_2136_);
lean_inc(v_a_2088_);
v___x_2137_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2133_, v_size_2136_, v_index_2135_, v_e_2066_, v_a_2088_);
lean_dec(v_index_2135_);
v___y_2114_ = v___x_2137_;
goto v___jp_2113_;
}
case 1:
{
lean_object* v_index_2138_; 
v_index_2138_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_index_2138_);
lean_dec_ref_known(v___x_2134_, 1);
v___y_2126_ = v___y_2133_;
v_i_2127_ = v_index_2138_;
goto v___jp_2125_;
}
default: 
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2133_, v___x_2139_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_index_2141_; 
v_index_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_index_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2126_ = v___y_2133_;
v_i_2127_ = v_index_2141_;
goto v___jp_2125_;
}
else
{
lean_dec_ref(v_e_2066_);
v___y_2114_ = v___y_2133_;
goto v___jp_2113_;
}
}
}
}
v___jp_2142_:
{
lean_object* v_size_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_size_2145_ = lean_ctor_get(v___y_2143_, 0);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_size_2145_, v___x_2146_);
lean_inc(v_a_2088_);
v___x_2148_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2143_, v___x_2147_, v_i_2144_, v_e_2066_, v_a_2088_);
lean_dec(v_i_2144_);
v___y_2114_ = v___x_2148_;
goto v___jp_2113_;
}
v___jp_2149_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_2108_);
lean_dec_ref(v_cache_2108_);
v___x_2151_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_2150_, v_e_2066_);
switch(lean_obj_tag(v___x_2151_))
{
case 0:
{
lean_object* v_index_2152_; lean_object* v_size_2153_; lean_object* v___x_2154_; 
v_index_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_index_2152_);
lean_dec_ref_known(v___x_2151_, 3);
v_size_2153_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_size_2153_);
lean_inc(v_a_2088_);
v___x_2154_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2150_, v_size_2153_, v_index_2152_, v_e_2066_, v_a_2088_);
lean_dec(v_index_2152_);
v___y_2114_ = v___x_2154_;
goto v___jp_2113_;
}
case 1:
{
lean_object* v_index_2155_; 
v_index_2155_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_index_2155_);
lean_dec_ref_known(v___x_2151_, 1);
v___y_2143_ = v___x_2150_;
v_i_2144_ = v_index_2155_;
goto v___jp_2142_;
}
default: 
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2150_, v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_index_2158_; 
v_index_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_index_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___y_2143_ = v___x_2150_;
v_i_2144_ = v_index_2158_;
goto v___jp_2142_;
}
else
{
lean_dec_ref(v_e_2066_);
v___y_2114_ = v___x_2150_;
goto v___jp_2113_;
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
lean_dec_ref(v_e_2066_);
return v___x_2087_;
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v_canon_2193_; lean_object* v_cacheInType_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_st_ref_get(v_a_2069_);
v_canon_2193_ = lean_ctor_get(v___x_2192_, 9);
lean_inc_ref(v_canon_2193_);
lean_dec(v___x_2192_);
v_cacheInType_2194_ = lean_ctor_get(v_canon_2193_, 1);
lean_inc_ref(v_cacheInType_2194_);
lean_dec_ref(v_canon_2193_);
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2194_, v_e_2066_);
lean_dec_ref(v_cacheInType_2194_);
if (lean_obj_tag(v___x_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_e_2066_);
lean_dec_ref(v_h_2065_);
lean_dec_ref(v_prop_2064_);
lean_dec_ref(v_g_2063_);
v_val_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 0);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_val_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_object* v___x_2204_; 
lean_dec(v___x_2195_);
lean_inc_ref(v_e_2066_);
v___x_2204_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2063_, v_prop_2064_, v_h_2065_, v_e_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2308_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2308_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2308_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v_canon_2210_; lean_object* v_share_2211_; lean_object* v_maxFVar_2212_; lean_object* v_proofInstInfo_2213_; lean_object* v_inferType_2214_; lean_object* v_getLevel_2215_; lean_object* v_congrInfo_2216_; lean_object* v_defEqI_2217_; lean_object* v_extensions_2218_; lean_object* v_issues_2219_; lean_object* v_instanceOverrides_2220_; uint8_t v_debug_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2307_; 
v___x_2209_ = lean_st_ref_take(v_a_2069_);
v_canon_2210_ = lean_ctor_get(v___x_2209_, 9);
v_share_2211_ = lean_ctor_get(v___x_2209_, 0);
v_maxFVar_2212_ = lean_ctor_get(v___x_2209_, 1);
v_proofInstInfo_2213_ = lean_ctor_get(v___x_2209_, 2);
v_inferType_2214_ = lean_ctor_get(v___x_2209_, 3);
v_getLevel_2215_ = lean_ctor_get(v___x_2209_, 4);
v_congrInfo_2216_ = lean_ctor_get(v___x_2209_, 5);
v_defEqI_2217_ = lean_ctor_get(v___x_2209_, 6);
v_extensions_2218_ = lean_ctor_get(v___x_2209_, 7);
v_issues_2219_ = lean_ctor_get(v___x_2209_, 8);
v_instanceOverrides_2220_ = lean_ctor_get(v___x_2209_, 10);
v_debug_2221_ = lean_ctor_get_uint8(v___x_2209_, sizeof(void*)*11);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2223_ = v___x_2209_;
v_isShared_2224_ = v_isSharedCheck_2307_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_instanceOverrides_2220_);
lean_inc(v_canon_2210_);
lean_inc(v_issues_2219_);
lean_inc(v_extensions_2218_);
lean_inc(v_defEqI_2217_);
lean_inc(v_congrInfo_2216_);
lean_inc(v_getLevel_2215_);
lean_inc(v_inferType_2214_);
lean_inc(v_proofInstInfo_2213_);
lean_inc(v_maxFVar_2212_);
lean_inc(v_share_2211_);
lean_dec(v___x_2209_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2307_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_cache_2225_; lean_object* v_cacheInType_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2306_; 
v_cache_2225_ = lean_ctor_get(v_canon_2210_, 0);
v_cacheInType_2226_ = lean_ctor_get(v_canon_2210_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_canon_2210_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2228_ = v_canon_2210_;
v_isShared_2229_ = v_isSharedCheck_2306_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_cacheInType_2226_);
lean_inc(v_cache_2225_);
lean_dec(v_canon_2210_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2306_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___y_2231_; lean_object* v___y_2243_; lean_object* v_i_2244_; lean_object* v___y_2260_; lean_object* v_i_2261_; lean_object* v___y_2267_; lean_object* v___x_2276_; 
v___x_2276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2226_, v_e_2066_);
switch(lean_obj_tag(v___x_2276_))
{
case 0:
{
lean_object* v_index_2277_; lean_object* v_size_2278_; lean_object* v___x_2279_; 
v_index_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_index_2277_);
lean_dec_ref_known(v___x_2276_, 3);
v_size_2278_ = lean_ctor_get(v_cacheInType_2226_, 0);
lean_inc(v_size_2278_);
lean_inc(v_a_2205_);
v___x_2279_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_2226_, v_size_2278_, v_index_2277_, v_e_2066_, v_a_2205_);
lean_dec(v_index_2277_);
v___y_2231_ = v___x_2279_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2280_; lean_object* v_size_2281_; lean_object* v_keyArray_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_index_2280_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_index_2280_);
lean_dec_ref_known(v___x_2276_, 1);
v_size_2281_ = lean_ctor_get(v_cacheInType_2226_, 0);
v_keyArray_2282_ = lean_ctor_get(v_cacheInType_2226_, 1);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_nat_add(v_size_2281_, v___x_2283_);
v___x_2285_ = lean_array_get_size(v_keyArray_2282_);
v___x_2286_ = lean_nat_dec_lt(v___x_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_dec(v___x_2284_);
lean_dec(v_index_2280_);
goto v___jp_2249_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2287_ = lean_unsigned_to_nat(4u);
v___x_2288_ = lean_nat_mul(v___x_2284_, v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(3u);
v___x_2290_ = lean_nat_mul(v___x_2285_, v___x_2289_);
v___x_2291_ = lean_nat_dec_le(v___x_2288_, v___x_2290_);
lean_dec(v___x_2290_);
lean_dec(v___x_2288_);
if (v___x_2291_ == 0)
{
lean_dec(v___x_2284_);
lean_dec(v_index_2280_);
goto v___jp_2249_;
}
else
{
lean_object* v___x_2292_; 
lean_inc(v_a_2205_);
v___x_2292_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_2226_, v___x_2284_, v_index_2280_, v_e_2066_, v_a_2205_);
lean_dec(v_index_2280_);
v___y_2231_ = v___x_2292_;
goto v___jp_2230_;
}
}
}
default: 
{
lean_object* v_size_2293_; lean_object* v_keyArray_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_size_2293_ = lean_ctor_get(v_cacheInType_2226_, 0);
v_keyArray_2294_ = lean_ctor_get(v_cacheInType_2226_, 1);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_nat_add(v_size_2293_, v___x_2295_);
v___x_2297_ = lean_array_get_size(v_keyArray_2294_);
v___x_2298_ = lean_nat_dec_lt(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
lean_dec(v___x_2296_);
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_2226_);
lean_dec_ref(v_cacheInType_2226_);
v___y_2267_ = v___x_2299_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2300_ = lean_unsigned_to_nat(4u);
v___x_2301_ = lean_nat_mul(v___x_2296_, v___x_2300_);
lean_dec(v___x_2296_);
v___x_2302_ = lean_unsigned_to_nat(3u);
v___x_2303_ = lean_nat_mul(v___x_2297_, v___x_2302_);
v___x_2304_ = lean_nat_dec_le(v___x_2301_, v___x_2303_);
lean_dec(v___x_2303_);
lean_dec(v___x_2301_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_2226_);
lean_dec_ref(v_cacheInType_2226_);
v___y_2267_ = v___x_2305_;
goto v___jp_2266_;
}
else
{
v___y_2267_ = v_cacheInType_2226_;
goto v___jp_2266_;
}
}
}
}
v___jp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v___y_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_cache_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___y_2231_);
v___x_2233_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 9, v___x_2233_);
v___x_2235_ = v___x_2223_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_share_2211_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_maxFVar_2212_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_proofInstInfo_2213_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_inferType_2214_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_getLevel_2215_);
lean_ctor_set(v_reuseFailAlloc_2240_, 5, v_congrInfo_2216_);
lean_ctor_set(v_reuseFailAlloc_2240_, 6, v_defEqI_2217_);
lean_ctor_set(v_reuseFailAlloc_2240_, 7, v_extensions_2218_);
lean_ctor_set(v_reuseFailAlloc_2240_, 8, v_issues_2219_);
lean_ctor_set(v_reuseFailAlloc_2240_, 9, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2240_, 10, v_instanceOverrides_2220_);
lean_ctor_set_uint8(v_reuseFailAlloc_2240_, sizeof(void*)*11, v_debug_2221_);
v___x_2235_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = lean_st_ref_put(v_a_2069_, v___x_2235_);
if (v_isShared_2208_ == 0)
{
v___x_2238_ = v___x_2207_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2205_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v___jp_2242_:
{
lean_object* v_size_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_size_2245_ = lean_ctor_get(v___y_2243_, 0);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_add(v_size_2245_, v___x_2246_);
lean_inc(v_a_2205_);
v___x_2248_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2243_, v___x_2247_, v_i_2244_, v_e_2066_, v_a_2205_);
lean_dec(v_i_2244_);
v___y_2231_ = v___x_2248_;
goto v___jp_2230_;
}
v___jp_2249_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_2226_);
lean_dec_ref(v_cacheInType_2226_);
v___x_2251_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_2250_, v_e_2066_);
switch(lean_obj_tag(v___x_2251_))
{
case 0:
{
lean_object* v_index_2252_; lean_object* v_size_2253_; lean_object* v___x_2254_; 
v_index_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_index_2252_);
lean_dec_ref_known(v___x_2251_, 3);
v_size_2253_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_size_2253_);
lean_inc(v_a_2205_);
v___x_2254_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2250_, v_size_2253_, v_index_2252_, v_e_2066_, v_a_2205_);
lean_dec(v_index_2252_);
v___y_2231_ = v___x_2254_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2255_; 
v_index_2255_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_index_2255_);
lean_dec_ref_known(v___x_2251_, 1);
v___y_2243_ = v___x_2250_;
v_i_2244_ = v_index_2255_;
goto v___jp_2242_;
}
default: 
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2250_, v___x_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_index_2258_; 
v_index_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_index_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___y_2243_ = v___x_2250_;
v_i_2244_ = v_index_2258_;
goto v___jp_2242_;
}
else
{
lean_dec_ref(v_e_2066_);
v___y_2231_ = v___x_2250_;
goto v___jp_2230_;
}
}
}
}
v___jp_2259_:
{
lean_object* v_size_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_size_2262_ = lean_ctor_get(v___y_2260_, 0);
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_add(v_size_2262_, v___x_2263_);
lean_inc(v_a_2205_);
v___x_2265_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2260_, v___x_2264_, v_i_2261_, v_e_2066_, v_a_2205_);
lean_dec(v_i_2261_);
v___y_2231_ = v___x_2265_;
goto v___jp_2230_;
}
v___jp_2266_:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_2267_, v_e_2066_);
switch(lean_obj_tag(v___x_2268_))
{
case 0:
{
lean_object* v_index_2269_; lean_object* v_size_2270_; lean_object* v___x_2271_; 
v_index_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_index_2269_);
lean_dec_ref_known(v___x_2268_, 3);
v_size_2270_ = lean_ctor_get(v___y_2267_, 0);
lean_inc(v_size_2270_);
lean_inc(v_a_2205_);
v___x_2271_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2267_, v_size_2270_, v_index_2269_, v_e_2066_, v_a_2205_);
lean_dec(v_index_2269_);
v___y_2231_ = v___x_2271_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2272_; 
v_index_2272_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_index_2272_);
lean_dec_ref_known(v___x_2268_, 1);
v___y_2260_ = v___y_2267_;
v_i_2261_ = v_index_2272_;
goto v___jp_2259_;
}
default: 
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2267_, v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_index_2275_; 
v_index_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_index_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___y_2260_ = v___y_2267_;
v_i_2261_ = v_index_2275_;
goto v___jp_2259_;
}
else
{
lean_dec_ref(v_e_2066_);
v___y_2231_ = v___y_2267_;
goto v___jp_2230_;
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
lean_dec_ref(v_e_2066_);
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2309_, lean_object* v_prop_2310_, lean_object* v_h_2311_, lean_object* v_e_2312_, uint8_t v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v_cacheInType_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v_i_2371_; lean_object* v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2400_; lean_object* v___y_2401_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v_i_2414_; lean_object* v___y_2420_; uint8_t v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v_a_2444_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2510_; lean_object* v___y_2511_; uint8_t v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v_i_2524_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v_i_2567_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2597_; 
if (v_a_2313_ == 0)
{
lean_object* v___x_2644_; lean_object* v_canon_2645_; lean_object* v_cache_2646_; lean_object* v___x_2647_; 
v___x_2644_ = lean_st_ref_get(v_a_2315_);
v_canon_2645_ = lean_ctor_get(v___x_2644_, 9);
lean_inc_ref(v_canon_2645_);
lean_dec(v___x_2644_);
v_cache_2646_ = lean_ctor_get(v_canon_2645_, 0);
lean_inc_ref(v_cache_2646_);
lean_dec_ref(v_canon_2645_);
v___x_2647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2646_, v_e_2312_);
lean_dec_ref(v_cache_2646_);
if (lean_obj_tag(v___x_2647_) == 1)
{
lean_object* v_val_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v_e_2312_);
lean_dec_ref(v_h_2311_);
lean_dec_ref(v_prop_2310_);
lean_dec_ref(v_g_2309_);
v_val_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_val_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 0);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_val_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v___x_2656_; 
lean_dec(v___x_2647_);
lean_inc_ref(v_prop_2310_);
v___x_2656_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2310_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_n(v_a_2657_, 2);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2657_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2665_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
if (lean_obj_tag(v_a_2659_) == 0)
{
lean_inc_ref(v_h_2311_);
v___y_2665_ = v_h_2311_;
goto v___jp_2664_;
}
else
{
lean_object* v_val_2672_; 
v_val_2672_ = lean_ctor_get(v_a_2659_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v_a_2659_, 1);
v___y_2665_ = v_val_2672_;
goto v___jp_2664_;
}
v___jp_2660_:
{
if (v___y_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_mkAppB(v_g_2309_, v_a_2657_, v___y_2661_);
v_a_2444_ = v___x_2663_;
goto v___jp_2443_;
}
else
{
lean_dec_ref(v___y_2661_);
lean_dec(v_a_2657_);
lean_dec_ref(v_g_2309_);
lean_inc_ref(v_e_2312_);
v_a_2444_ = v_e_2312_;
goto v___jp_2443_;
}
}
v___jp_2664_:
{
size_t v___x_2666_; size_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2666_ = lean_ptr_addr(v_prop_2310_);
lean_dec_ref(v_prop_2310_);
v___x_2667_ = lean_ptr_addr(v_a_2657_);
v___x_2668_ = lean_usize_dec_eq(v___x_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_dec_ref(v_h_2311_);
v___y_2661_ = v___y_2665_;
v___y_2662_ = v___x_2668_;
goto v___jp_2660_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2669_ = lean_ptr_addr(v_h_2311_);
lean_dec_ref(v_h_2311_);
v___x_2670_ = lean_ptr_addr(v___y_2665_);
v___x_2671_ = lean_usize_dec_eq(v___x_2669_, v___x_2670_);
v___y_2661_ = v___y_2665_;
v___y_2662_ = v___x_2671_;
goto v___jp_2660_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_a_2657_);
lean_dec_ref(v_e_2312_);
lean_dec_ref(v_h_2311_);
lean_dec_ref(v_prop_2310_);
lean_dec_ref(v_g_2309_);
v_a_2673_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2658_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2658_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_dec_ref(v_h_2311_);
lean_dec_ref(v_prop_2310_);
lean_dec_ref(v_g_2309_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2656_, 1);
v_a_2444_ = v_a_2681_;
goto v___jp_2443_;
}
else
{
lean_dec_ref(v_e_2312_);
return v___x_2656_;
}
}
}
}
else
{
lean_object* v___x_2682_; lean_object* v_canon_2683_; lean_object* v_cacheInType_2684_; lean_object* v___x_2685_; 
lean_dec_ref(v_g_2309_);
v___x_2682_ = lean_st_ref_get(v_a_2315_);
v_canon_2683_ = lean_ctor_get(v___x_2682_, 9);
lean_inc_ref(v_canon_2683_);
lean_dec(v___x_2682_);
v_cacheInType_2684_ = lean_ctor_get(v_canon_2683_, 1);
lean_inc_ref(v_cacheInType_2684_);
lean_dec_ref(v_canon_2683_);
v___x_2685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2684_, v_e_2312_);
lean_dec_ref(v_cacheInType_2684_);
if (lean_obj_tag(v___x_2685_) == 1)
{
lean_object* v_val_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_e_2312_);
lean_dec_ref(v_h_2311_);
lean_dec_ref(v_prop_2310_);
v_val_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_val_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 0);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_val_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v___x_2694_; 
lean_dec(v___x_2685_);
v___x_2694_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2310_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = 0;
v___x_2697_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2311_, v_a_2695_, v___x_2696_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
v___y_2597_ = v___x_2697_;
goto v___jp_2596_;
}
else
{
lean_dec_ref(v_h_2311_);
v___y_2597_ = v___x_2694_;
goto v___jp_2596_;
}
}
}
v___jp_2321_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2335_);
lean_ctor_set(v___x_2336_, 1, v_cacheInType_2327_);
v___x_2337_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2337_, 0, v___y_2328_);
lean_ctor_set(v___x_2337_, 1, v___y_2330_);
lean_ctor_set(v___x_2337_, 2, v___y_2334_);
lean_ctor_set(v___x_2337_, 3, v___y_2332_);
lean_ctor_set(v___x_2337_, 4, v___y_2333_);
lean_ctor_set(v___x_2337_, 5, v___y_2322_);
lean_ctor_set(v___x_2337_, 6, v___y_2326_);
lean_ctor_set(v___x_2337_, 7, v___y_2329_);
lean_ctor_set(v___x_2337_, 8, v___y_2324_);
lean_ctor_set(v___x_2337_, 9, v___x_2336_);
lean_ctor_set(v___x_2337_, 10, v___y_2325_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*11, v___y_2323_);
v___x_2338_ = lean_st_ref_put(v_a_2315_, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___y_2331_);
return v___x_2339_;
}
v___jp_2340_:
{
lean_object* v_cacheInType_2355_; 
v_cacheInType_2355_ = lean_ctor_get(v___y_2346_, 1);
lean_inc_ref(v_cacheInType_2355_);
lean_dec_ref(v___y_2346_);
v___y_2322_ = v___y_2341_;
v___y_2323_ = v___y_2342_;
v___y_2324_ = v___y_2343_;
v___y_2325_ = v___y_2344_;
v___y_2326_ = v___y_2345_;
v_cacheInType_2327_ = v_cacheInType_2355_;
v___y_2328_ = v___y_2347_;
v___y_2329_ = v___y_2348_;
v___y_2330_ = v___y_2349_;
v___y_2331_ = v___y_2350_;
v___y_2332_ = v___y_2351_;
v___y_2333_ = v___y_2352_;
v___y_2334_ = v___y_2353_;
v___y_2335_ = v___y_2354_;
goto v___jp_2321_;
}
v___jp_2356_:
{
lean_object* v_size_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_size_2372_ = lean_ctor_get(v___y_2369_, 0);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_size_2372_, v___x_2373_);
lean_inc_ref(v___y_2366_);
v___x_2375_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2369_, v___x_2374_, v_i_2371_, v_e_2312_, v___y_2366_);
lean_dec(v_i_2371_);
v___y_2341_ = v___y_2357_;
v___y_2342_ = v___y_2358_;
v___y_2343_ = v___y_2359_;
v___y_2344_ = v___y_2360_;
v___y_2345_ = v___y_2361_;
v___y_2346_ = v___y_2362_;
v___y_2347_ = v___y_2363_;
v___y_2348_ = v___y_2364_;
v___y_2349_ = v___y_2365_;
v___y_2350_ = v___y_2366_;
v___y_2351_ = v___y_2367_;
v___y_2352_ = v___y_2368_;
v___y_2353_ = v___y_2370_;
v___y_2354_ = v___x_2375_;
goto v___jp_2340_;
}
v___jp_2376_:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_2390_, v_e_2312_);
switch(lean_obj_tag(v___x_2391_))
{
case 0:
{
lean_object* v_index_2392_; lean_object* v_size_2393_; lean_object* v___x_2394_; 
v_index_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_index_2392_);
lean_dec_ref_known(v___x_2391_, 3);
v_size_2393_ = lean_ctor_get(v___y_2390_, 0);
lean_inc(v_size_2393_);
lean_inc_ref(v___y_2386_);
v___x_2394_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2390_, v_size_2393_, v_index_2392_, v_e_2312_, v___y_2386_);
lean_dec(v_index_2392_);
v___y_2341_ = v___y_2377_;
v___y_2342_ = v___y_2378_;
v___y_2343_ = v___y_2379_;
v___y_2344_ = v___y_2380_;
v___y_2345_ = v___y_2381_;
v___y_2346_ = v___y_2382_;
v___y_2347_ = v___y_2383_;
v___y_2348_ = v___y_2384_;
v___y_2349_ = v___y_2385_;
v___y_2350_ = v___y_2386_;
v___y_2351_ = v___y_2387_;
v___y_2352_ = v___y_2388_;
v___y_2353_ = v___y_2389_;
v___y_2354_ = v___x_2394_;
goto v___jp_2340_;
}
case 1:
{
lean_object* v_index_2395_; 
v_index_2395_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_index_2395_);
lean_dec_ref_known(v___x_2391_, 1);
v___y_2357_ = v___y_2377_;
v___y_2358_ = v___y_2378_;
v___y_2359_ = v___y_2379_;
v___y_2360_ = v___y_2380_;
v___y_2361_ = v___y_2381_;
v___y_2362_ = v___y_2382_;
v___y_2363_ = v___y_2383_;
v___y_2364_ = v___y_2384_;
v___y_2365_ = v___y_2385_;
v___y_2366_ = v___y_2386_;
v___y_2367_ = v___y_2387_;
v___y_2368_ = v___y_2388_;
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___y_2389_;
v_i_2371_ = v_index_2395_;
goto v___jp_2356_;
}
default: 
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2390_, v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_index_2398_; 
v_index_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_index_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___y_2357_ = v___y_2377_;
v___y_2358_ = v___y_2378_;
v___y_2359_ = v___y_2379_;
v___y_2360_ = v___y_2380_;
v___y_2361_ = v___y_2381_;
v___y_2362_ = v___y_2382_;
v___y_2363_ = v___y_2383_;
v___y_2364_ = v___y_2384_;
v___y_2365_ = v___y_2385_;
v___y_2366_ = v___y_2386_;
v___y_2367_ = v___y_2387_;
v___y_2368_ = v___y_2388_;
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___y_2389_;
v_i_2371_ = v_index_2398_;
goto v___jp_2356_;
}
else
{
lean_dec_ref(v_e_2312_);
v___y_2341_ = v___y_2377_;
v___y_2342_ = v___y_2378_;
v___y_2343_ = v___y_2379_;
v___y_2344_ = v___y_2380_;
v___y_2345_ = v___y_2381_;
v___y_2346_ = v___y_2382_;
v___y_2347_ = v___y_2383_;
v___y_2348_ = v___y_2384_;
v___y_2349_ = v___y_2385_;
v___y_2350_ = v___y_2386_;
v___y_2351_ = v___y_2387_;
v___y_2352_ = v___y_2388_;
v___y_2353_ = v___y_2389_;
v___y_2354_ = v___y_2390_;
goto v___jp_2340_;
}
}
}
}
v___jp_2399_:
{
lean_object* v_size_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_size_2415_ = lean_ctor_get(v___y_2400_, 0);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_add(v_size_2415_, v___x_2416_);
lean_inc_ref(v___y_2410_);
v___x_2418_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2400_, v___x_2417_, v_i_2414_, v_e_2312_, v___y_2410_);
lean_dec(v_i_2414_);
v___y_2341_ = v___y_2401_;
v___y_2342_ = v___y_2402_;
v___y_2343_ = v___y_2403_;
v___y_2344_ = v___y_2404_;
v___y_2345_ = v___y_2405_;
v___y_2346_ = v___y_2406_;
v___y_2347_ = v___y_2407_;
v___y_2348_ = v___y_2408_;
v___y_2349_ = v___y_2409_;
v___y_2350_ = v___y_2410_;
v___y_2351_ = v___y_2411_;
v___y_2352_ = v___y_2412_;
v___y_2353_ = v___y_2413_;
v___y_2354_ = v___x_2418_;
goto v___jp_2340_;
}
v___jp_2419_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v___y_2426_);
lean_dec_ref(v___y_2426_);
v___x_2435_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_2434_, v_e_2312_);
switch(lean_obj_tag(v___x_2435_))
{
case 0:
{
lean_object* v_index_2436_; lean_object* v_size_2437_; lean_object* v___x_2438_; 
v_index_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_index_2436_);
lean_dec_ref_known(v___x_2435_, 3);
v_size_2437_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_size_2437_);
lean_inc_ref(v___y_2430_);
v___x_2438_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2434_, v_size_2437_, v_index_2436_, v_e_2312_, v___y_2430_);
lean_dec(v_index_2436_);
v___y_2341_ = v___y_2420_;
v___y_2342_ = v___y_2421_;
v___y_2343_ = v___y_2422_;
v___y_2344_ = v___y_2423_;
v___y_2345_ = v___y_2424_;
v___y_2346_ = v___y_2425_;
v___y_2347_ = v___y_2427_;
v___y_2348_ = v___y_2428_;
v___y_2349_ = v___y_2429_;
v___y_2350_ = v___y_2430_;
v___y_2351_ = v___y_2431_;
v___y_2352_ = v___y_2432_;
v___y_2353_ = v___y_2433_;
v___y_2354_ = v___x_2438_;
goto v___jp_2340_;
}
case 1:
{
lean_object* v_index_2439_; 
v_index_2439_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_index_2439_);
lean_dec_ref_known(v___x_2435_, 1);
v___y_2400_ = v___x_2434_;
v___y_2401_ = v___y_2420_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___y_2422_;
v___y_2404_ = v___y_2423_;
v___y_2405_ = v___y_2424_;
v___y_2406_ = v___y_2425_;
v___y_2407_ = v___y_2427_;
v___y_2408_ = v___y_2428_;
v___y_2409_ = v___y_2429_;
v___y_2410_ = v___y_2430_;
v___y_2411_ = v___y_2431_;
v___y_2412_ = v___y_2432_;
v___y_2413_ = v___y_2433_;
v_i_2414_ = v_index_2439_;
goto v___jp_2399_;
}
default: 
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2434_, v___x_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_index_2442_; 
v_index_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_index_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___y_2400_ = v___x_2434_;
v___y_2401_ = v___y_2420_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___y_2422_;
v___y_2404_ = v___y_2423_;
v___y_2405_ = v___y_2424_;
v___y_2406_ = v___y_2425_;
v___y_2407_ = v___y_2427_;
v___y_2408_ = v___y_2428_;
v___y_2409_ = v___y_2429_;
v___y_2410_ = v___y_2430_;
v___y_2411_ = v___y_2431_;
v___y_2412_ = v___y_2432_;
v___y_2413_ = v___y_2433_;
v_i_2414_ = v_index_2442_;
goto v___jp_2399_;
}
else
{
lean_dec_ref(v_e_2312_);
v___y_2341_ = v___y_2420_;
v___y_2342_ = v___y_2421_;
v___y_2343_ = v___y_2422_;
v___y_2344_ = v___y_2423_;
v___y_2345_ = v___y_2424_;
v___y_2346_ = v___y_2425_;
v___y_2347_ = v___y_2427_;
v___y_2348_ = v___y_2428_;
v___y_2349_ = v___y_2429_;
v___y_2350_ = v___y_2430_;
v___y_2351_ = v___y_2431_;
v___y_2352_ = v___y_2432_;
v___y_2353_ = v___y_2433_;
v___y_2354_ = v___x_2434_;
goto v___jp_2340_;
}
}
}
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v_canon_2446_; lean_object* v_share_2447_; lean_object* v_maxFVar_2448_; lean_object* v_proofInstInfo_2449_; lean_object* v_inferType_2450_; lean_object* v_getLevel_2451_; lean_object* v_congrInfo_2452_; lean_object* v_defEqI_2453_; lean_object* v_extensions_2454_; lean_object* v_issues_2455_; lean_object* v_instanceOverrides_2456_; uint8_t v_debug_2457_; lean_object* v_cache_2458_; lean_object* v_cacheInType_2459_; lean_object* v___x_2460_; 
v___x_2445_ = lean_st_ref_take(v_a_2315_);
v_canon_2446_ = lean_ctor_get(v___x_2445_, 9);
lean_inc_ref(v_canon_2446_);
v_share_2447_ = lean_ctor_get(v___x_2445_, 0);
lean_inc_ref(v_share_2447_);
v_maxFVar_2448_ = lean_ctor_get(v___x_2445_, 1);
lean_inc_ref(v_maxFVar_2448_);
v_proofInstInfo_2449_ = lean_ctor_get(v___x_2445_, 2);
lean_inc_ref(v_proofInstInfo_2449_);
v_inferType_2450_ = lean_ctor_get(v___x_2445_, 3);
lean_inc_ref(v_inferType_2450_);
v_getLevel_2451_ = lean_ctor_get(v___x_2445_, 4);
lean_inc_ref(v_getLevel_2451_);
v_congrInfo_2452_ = lean_ctor_get(v___x_2445_, 5);
lean_inc_ref(v_congrInfo_2452_);
v_defEqI_2453_ = lean_ctor_get(v___x_2445_, 6);
lean_inc_ref(v_defEqI_2453_);
v_extensions_2454_ = lean_ctor_get(v___x_2445_, 7);
lean_inc_ref(v_extensions_2454_);
v_issues_2455_ = lean_ctor_get(v___x_2445_, 8);
lean_inc(v_issues_2455_);
v_instanceOverrides_2456_ = lean_ctor_get(v___x_2445_, 10);
lean_inc_ref(v_instanceOverrides_2456_);
v_debug_2457_ = lean_ctor_get_uint8(v___x_2445_, sizeof(void*)*11);
lean_dec(v___x_2445_);
v_cache_2458_ = lean_ctor_get(v_canon_2446_, 0);
v_cacheInType_2459_ = lean_ctor_get(v_canon_2446_, 1);
v___x_2460_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2458_, v_e_2312_);
switch(lean_obj_tag(v___x_2460_))
{
case 0:
{
lean_object* v_index_2461_; lean_object* v_size_2462_; lean_object* v___x_2463_; 
lean_inc_ref(v_cacheInType_2459_);
lean_inc_ref(v_cache_2458_);
lean_dec_ref(v_canon_2446_);
v_index_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_index_2461_);
lean_dec_ref_known(v___x_2460_, 3);
v_size_2462_ = lean_ctor_get(v_cache_2458_, 0);
lean_inc(v_size_2462_);
lean_inc_ref(v_a_2444_);
v___x_2463_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2458_, v_size_2462_, v_index_2461_, v_e_2312_, v_a_2444_);
lean_dec(v_index_2461_);
v___y_2322_ = v_congrInfo_2452_;
v___y_2323_ = v_debug_2457_;
v___y_2324_ = v_issues_2455_;
v___y_2325_ = v_instanceOverrides_2456_;
v___y_2326_ = v_defEqI_2453_;
v_cacheInType_2327_ = v_cacheInType_2459_;
v___y_2328_ = v_share_2447_;
v___y_2329_ = v_extensions_2454_;
v___y_2330_ = v_maxFVar_2448_;
v___y_2331_ = v_a_2444_;
v___y_2332_ = v_inferType_2450_;
v___y_2333_ = v_getLevel_2451_;
v___y_2334_ = v_proofInstInfo_2449_;
v___y_2335_ = v___x_2463_;
goto v___jp_2321_;
}
case 1:
{
lean_object* v_index_2464_; lean_object* v_size_2465_; lean_object* v_keyArray_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
lean_inc_ref(v_cache_2458_);
v_index_2464_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_index_2464_);
lean_dec_ref_known(v___x_2460_, 1);
v_size_2465_ = lean_ctor_get(v_cache_2458_, 0);
v_keyArray_2466_ = lean_ctor_get(v_cache_2458_, 1);
v___x_2467_ = lean_unsigned_to_nat(1u);
v___x_2468_ = lean_nat_add(v_size_2465_, v___x_2467_);
v___x_2469_ = lean_array_get_size(v_keyArray_2466_);
v___x_2470_ = lean_nat_dec_lt(v___x_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec(v___x_2468_);
lean_dec(v_index_2464_);
v___y_2420_ = v_congrInfo_2452_;
v___y_2421_ = v_debug_2457_;
v___y_2422_ = v_issues_2455_;
v___y_2423_ = v_instanceOverrides_2456_;
v___y_2424_ = v_defEqI_2453_;
v___y_2425_ = v_canon_2446_;
v___y_2426_ = v_cache_2458_;
v___y_2427_ = v_share_2447_;
v___y_2428_ = v_extensions_2454_;
v___y_2429_ = v_maxFVar_2448_;
v___y_2430_ = v_a_2444_;
v___y_2431_ = v_inferType_2450_;
v___y_2432_ = v_getLevel_2451_;
v___y_2433_ = v_proofInstInfo_2449_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2471_ = lean_unsigned_to_nat(4u);
v___x_2472_ = lean_nat_mul(v___x_2468_, v___x_2471_);
v___x_2473_ = lean_unsigned_to_nat(3u);
v___x_2474_ = lean_nat_mul(v___x_2469_, v___x_2473_);
v___x_2475_ = lean_nat_dec_le(v___x_2472_, v___x_2474_);
lean_dec(v___x_2474_);
lean_dec(v___x_2472_);
if (v___x_2475_ == 0)
{
lean_dec(v___x_2468_);
lean_dec(v_index_2464_);
v___y_2420_ = v_congrInfo_2452_;
v___y_2421_ = v_debug_2457_;
v___y_2422_ = v_issues_2455_;
v___y_2423_ = v_instanceOverrides_2456_;
v___y_2424_ = v_defEqI_2453_;
v___y_2425_ = v_canon_2446_;
v___y_2426_ = v_cache_2458_;
v___y_2427_ = v_share_2447_;
v___y_2428_ = v_extensions_2454_;
v___y_2429_ = v_maxFVar_2448_;
v___y_2430_ = v_a_2444_;
v___y_2431_ = v_inferType_2450_;
v___y_2432_ = v_getLevel_2451_;
v___y_2433_ = v_proofInstInfo_2449_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2476_; 
lean_inc_ref(v_cacheInType_2459_);
lean_dec_ref(v_canon_2446_);
lean_inc_ref(v_a_2444_);
v___x_2476_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2458_, v___x_2468_, v_index_2464_, v_e_2312_, v_a_2444_);
lean_dec(v_index_2464_);
v___y_2322_ = v_congrInfo_2452_;
v___y_2323_ = v_debug_2457_;
v___y_2324_ = v_issues_2455_;
v___y_2325_ = v_instanceOverrides_2456_;
v___y_2326_ = v_defEqI_2453_;
v_cacheInType_2327_ = v_cacheInType_2459_;
v___y_2328_ = v_share_2447_;
v___y_2329_ = v_extensions_2454_;
v___y_2330_ = v_maxFVar_2448_;
v___y_2331_ = v_a_2444_;
v___y_2332_ = v_inferType_2450_;
v___y_2333_ = v_getLevel_2451_;
v___y_2334_ = v_proofInstInfo_2449_;
v___y_2335_ = v___x_2476_;
goto v___jp_2321_;
}
}
}
default: 
{
lean_object* v_size_2477_; lean_object* v_keyArray_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_size_2477_ = lean_ctor_get(v_cache_2458_, 0);
v_keyArray_2478_ = lean_ctor_get(v_cache_2458_, 1);
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_size_2477_, v___x_2479_);
v___x_2481_ = lean_array_get_size(v_keyArray_2478_);
v___x_2482_ = lean_nat_dec_lt(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
lean_dec(v___x_2480_);
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_2458_);
v___y_2377_ = v_congrInfo_2452_;
v___y_2378_ = v_debug_2457_;
v___y_2379_ = v_issues_2455_;
v___y_2380_ = v_instanceOverrides_2456_;
v___y_2381_ = v_defEqI_2453_;
v___y_2382_ = v_canon_2446_;
v___y_2383_ = v_share_2447_;
v___y_2384_ = v_extensions_2454_;
v___y_2385_ = v_maxFVar_2448_;
v___y_2386_ = v_a_2444_;
v___y_2387_ = v_inferType_2450_;
v___y_2388_ = v_getLevel_2451_;
v___y_2389_ = v_proofInstInfo_2449_;
v___y_2390_ = v___x_2483_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2484_ = lean_unsigned_to_nat(4u);
v___x_2485_ = lean_nat_mul(v___x_2480_, v___x_2484_);
lean_dec(v___x_2480_);
v___x_2486_ = lean_unsigned_to_nat(3u);
v___x_2487_ = lean_nat_mul(v___x_2481_, v___x_2486_);
v___x_2488_ = lean_nat_dec_le(v___x_2485_, v___x_2487_);
lean_dec(v___x_2487_);
lean_dec(v___x_2485_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_2458_);
v___y_2377_ = v_congrInfo_2452_;
v___y_2378_ = v_debug_2457_;
v___y_2379_ = v_issues_2455_;
v___y_2380_ = v_instanceOverrides_2456_;
v___y_2381_ = v_defEqI_2453_;
v___y_2382_ = v_canon_2446_;
v___y_2383_ = v_share_2447_;
v___y_2384_ = v_extensions_2454_;
v___y_2385_ = v_maxFVar_2448_;
v___y_2386_ = v_a_2444_;
v___y_2387_ = v_inferType_2450_;
v___y_2388_ = v_getLevel_2451_;
v___y_2389_ = v_proofInstInfo_2449_;
v___y_2390_ = v___x_2489_;
goto v___jp_2376_;
}
else
{
lean_inc_ref(v_cache_2458_);
v___y_2377_ = v_congrInfo_2452_;
v___y_2378_ = v_debug_2457_;
v___y_2379_ = v_issues_2455_;
v___y_2380_ = v_instanceOverrides_2456_;
v___y_2381_ = v_defEqI_2453_;
v___y_2382_ = v_canon_2446_;
v___y_2383_ = v_share_2447_;
v___y_2384_ = v_extensions_2454_;
v___y_2385_ = v_maxFVar_2448_;
v___y_2386_ = v_a_2444_;
v___y_2387_ = v_inferType_2450_;
v___y_2388_ = v_getLevel_2451_;
v___y_2389_ = v_proofInstInfo_2449_;
v___y_2390_ = v_cache_2458_;
goto v___jp_2376_;
}
}
}
}
}
v___jp_2490_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___y_2495_);
lean_ctor_set(v___x_2505_, 1, v___y_2504_);
v___x_2506_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2506_, 0, v___y_2502_);
lean_ctor_set(v___x_2506_, 1, v___y_2492_);
lean_ctor_set(v___x_2506_, 2, v___y_2497_);
lean_ctor_set(v___x_2506_, 3, v___y_2498_);
lean_ctor_set(v___x_2506_, 4, v___y_2503_);
lean_ctor_set(v___x_2506_, 5, v___y_2496_);
lean_ctor_set(v___x_2506_, 6, v___y_2491_);
lean_ctor_set(v___x_2506_, 7, v___y_2501_);
lean_ctor_set(v___x_2506_, 8, v___y_2494_);
lean_ctor_set(v___x_2506_, 9, v___x_2505_);
lean_ctor_set(v___x_2506_, 10, v___y_2500_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*11, v___y_2493_);
v___x_2507_ = lean_st_ref_put(v_a_2315_, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2499_);
return v___x_2508_;
}
v___jp_2509_:
{
lean_object* v_size_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_size_2525_ = lean_ctor_get(v___y_2520_, 0);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_nat_add(v_size_2525_, v___x_2526_);
lean_inc_ref(v___y_2516_);
v___x_2528_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2520_, v___x_2527_, v_i_2524_, v_e_2312_, v___y_2516_);
lean_dec(v_i_2524_);
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___y_2511_;
v___y_2493_ = v___y_2512_;
v___y_2494_ = v___y_2515_;
v___y_2495_ = v___y_2517_;
v___y_2496_ = v___y_2518_;
v___y_2497_ = v___y_2513_;
v___y_2498_ = v___y_2514_;
v___y_2499_ = v___y_2516_;
v___y_2500_ = v___y_2519_;
v___y_2501_ = v___y_2521_;
v___y_2502_ = v___y_2522_;
v___y_2503_ = v___y_2523_;
v___y_2504_ = v___x_2528_;
goto v___jp_2490_;
}
v___jp_2529_:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_2543_, v_e_2312_);
switch(lean_obj_tag(v___x_2544_))
{
case 0:
{
lean_object* v_index_2545_; lean_object* v_size_2546_; lean_object* v___x_2547_; 
v_index_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_index_2545_);
lean_dec_ref_known(v___x_2544_, 3);
v_size_2546_ = lean_ctor_get(v___y_2543_, 0);
lean_inc(v_size_2546_);
lean_inc_ref(v___y_2538_);
v___x_2547_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2543_, v_size_2546_, v_index_2545_, v_e_2312_, v___y_2538_);
lean_dec(v_index_2545_);
v___y_2491_ = v___y_2530_;
v___y_2492_ = v___y_2531_;
v___y_2493_ = v___y_2532_;
v___y_2494_ = v___y_2537_;
v___y_2495_ = v___y_2533_;
v___y_2496_ = v___y_2535_;
v___y_2497_ = v___y_2534_;
v___y_2498_ = v___y_2536_;
v___y_2499_ = v___y_2538_;
v___y_2500_ = v___y_2539_;
v___y_2501_ = v___y_2540_;
v___y_2502_ = v___y_2541_;
v___y_2503_ = v___y_2542_;
v___y_2504_ = v___x_2547_;
goto v___jp_2490_;
}
case 1:
{
lean_object* v_index_2548_; 
v_index_2548_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_index_2548_);
lean_dec_ref_known(v___x_2544_, 1);
v___y_2510_ = v___y_2530_;
v___y_2511_ = v___y_2531_;
v___y_2512_ = v___y_2532_;
v___y_2513_ = v___y_2534_;
v___y_2514_ = v___y_2536_;
v___y_2515_ = v___y_2537_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2533_;
v___y_2518_ = v___y_2535_;
v___y_2519_ = v___y_2539_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2540_;
v___y_2522_ = v___y_2541_;
v___y_2523_ = v___y_2542_;
v_i_2524_ = v_index_2548_;
goto v___jp_2509_;
}
default: 
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2543_, v___x_2549_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_index_2551_; 
v_index_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_index_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___y_2510_ = v___y_2530_;
v___y_2511_ = v___y_2531_;
v___y_2512_ = v___y_2532_;
v___y_2513_ = v___y_2534_;
v___y_2514_ = v___y_2536_;
v___y_2515_ = v___y_2537_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2533_;
v___y_2518_ = v___y_2535_;
v___y_2519_ = v___y_2539_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2540_;
v___y_2522_ = v___y_2541_;
v___y_2523_ = v___y_2542_;
v_i_2524_ = v_index_2551_;
goto v___jp_2509_;
}
else
{
lean_dec_ref(v_e_2312_);
v___y_2491_ = v___y_2530_;
v___y_2492_ = v___y_2531_;
v___y_2493_ = v___y_2532_;
v___y_2494_ = v___y_2537_;
v___y_2495_ = v___y_2533_;
v___y_2496_ = v___y_2535_;
v___y_2497_ = v___y_2534_;
v___y_2498_ = v___y_2536_;
v___y_2499_ = v___y_2538_;
v___y_2500_ = v___y_2539_;
v___y_2501_ = v___y_2540_;
v___y_2502_ = v___y_2541_;
v___y_2503_ = v___y_2542_;
v___y_2504_ = v___y_2543_;
goto v___jp_2490_;
}
}
}
}
v___jp_2552_:
{
lean_object* v_size_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_size_2568_ = lean_ctor_get(v___y_2554_, 0);
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_add(v_size_2568_, v___x_2569_);
lean_inc_ref(v___y_2560_);
v___x_2571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2554_, v___x_2570_, v_i_2567_, v_e_2312_, v___y_2560_);
lean_dec(v_i_2567_);
v___y_2491_ = v___y_2553_;
v___y_2492_ = v___y_2555_;
v___y_2493_ = v___y_2556_;
v___y_2494_ = v___y_2559_;
v___y_2495_ = v___y_2561_;
v___y_2496_ = v___y_2562_;
v___y_2497_ = v___y_2557_;
v___y_2498_ = v___y_2558_;
v___y_2499_ = v___y_2560_;
v___y_2500_ = v___y_2563_;
v___y_2501_ = v___y_2564_;
v___y_2502_ = v___y_2565_;
v___y_2503_ = v___y_2566_;
v___y_2504_ = v___x_2571_;
goto v___jp_2490_;
}
v___jp_2572_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v___y_2580_);
lean_dec_ref(v___y_2580_);
v___x_2588_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_2587_, v_e_2312_);
switch(lean_obj_tag(v___x_2588_))
{
case 0:
{
lean_object* v_index_2589_; lean_object* v_size_2590_; lean_object* v___x_2591_; 
v_index_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_index_2589_);
lean_dec_ref_known(v___x_2588_, 3);
v_size_2590_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_size_2590_);
lean_inc_ref(v___y_2582_);
v___x_2591_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2587_, v_size_2590_, v_index_2589_, v_e_2312_, v___y_2582_);
lean_dec(v_index_2589_);
v___y_2491_ = v___y_2573_;
v___y_2492_ = v___y_2574_;
v___y_2493_ = v___y_2575_;
v___y_2494_ = v___y_2581_;
v___y_2495_ = v___y_2576_;
v___y_2496_ = v___y_2578_;
v___y_2497_ = v___y_2577_;
v___y_2498_ = v___y_2579_;
v___y_2499_ = v___y_2582_;
v___y_2500_ = v___y_2583_;
v___y_2501_ = v___y_2584_;
v___y_2502_ = v___y_2585_;
v___y_2503_ = v___y_2586_;
v___y_2504_ = v___x_2591_;
goto v___jp_2490_;
}
case 1:
{
lean_object* v_index_2592_; 
v_index_2592_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_index_2592_);
lean_dec_ref_known(v___x_2588_, 1);
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___x_2587_;
v___y_2555_ = v___y_2574_;
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___y_2577_;
v___y_2558_ = v___y_2579_;
v___y_2559_ = v___y_2581_;
v___y_2560_ = v___y_2582_;
v___y_2561_ = v___y_2576_;
v___y_2562_ = v___y_2578_;
v___y_2563_ = v___y_2583_;
v___y_2564_ = v___y_2584_;
v___y_2565_ = v___y_2585_;
v___y_2566_ = v___y_2586_;
v_i_2567_ = v_index_2592_;
goto v___jp_2552_;
}
default: 
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2587_, v___x_2593_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_index_2595_; 
v_index_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_index_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___x_2587_;
v___y_2555_ = v___y_2574_;
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___y_2577_;
v___y_2558_ = v___y_2579_;
v___y_2559_ = v___y_2581_;
v___y_2560_ = v___y_2582_;
v___y_2561_ = v___y_2576_;
v___y_2562_ = v___y_2578_;
v___y_2563_ = v___y_2583_;
v___y_2564_ = v___y_2584_;
v___y_2565_ = v___y_2585_;
v___y_2566_ = v___y_2586_;
v_i_2567_ = v_index_2595_;
goto v___jp_2552_;
}
else
{
lean_dec_ref(v_e_2312_);
v___y_2491_ = v___y_2573_;
v___y_2492_ = v___y_2574_;
v___y_2493_ = v___y_2575_;
v___y_2494_ = v___y_2581_;
v___y_2495_ = v___y_2576_;
v___y_2496_ = v___y_2578_;
v___y_2497_ = v___y_2577_;
v___y_2498_ = v___y_2579_;
v___y_2499_ = v___y_2582_;
v___y_2500_ = v___y_2583_;
v___y_2501_ = v___y_2584_;
v___y_2502_ = v___y_2585_;
v___y_2503_ = v___y_2586_;
v___y_2504_ = v___x_2587_;
goto v___jp_2490_;
}
}
}
}
v___jp_2596_:
{
if (lean_obj_tag(v___y_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v_canon_2600_; lean_object* v_share_2601_; lean_object* v_maxFVar_2602_; lean_object* v_proofInstInfo_2603_; lean_object* v_inferType_2604_; lean_object* v_getLevel_2605_; lean_object* v_congrInfo_2606_; lean_object* v_defEqI_2607_; lean_object* v_extensions_2608_; lean_object* v_issues_2609_; lean_object* v_instanceOverrides_2610_; uint8_t v_debug_2611_; lean_object* v_cache_2612_; lean_object* v_cacheInType_2613_; lean_object* v___x_2614_; 
v_a_2598_ = lean_ctor_get(v___y_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___y_2597_, 1);
v___x_2599_ = lean_st_ref_take(v_a_2315_);
v_canon_2600_ = lean_ctor_get(v___x_2599_, 9);
lean_inc_ref(v_canon_2600_);
v_share_2601_ = lean_ctor_get(v___x_2599_, 0);
lean_inc_ref(v_share_2601_);
v_maxFVar_2602_ = lean_ctor_get(v___x_2599_, 1);
lean_inc_ref(v_maxFVar_2602_);
v_proofInstInfo_2603_ = lean_ctor_get(v___x_2599_, 2);
lean_inc_ref(v_proofInstInfo_2603_);
v_inferType_2604_ = lean_ctor_get(v___x_2599_, 3);
lean_inc_ref(v_inferType_2604_);
v_getLevel_2605_ = lean_ctor_get(v___x_2599_, 4);
lean_inc_ref(v_getLevel_2605_);
v_congrInfo_2606_ = lean_ctor_get(v___x_2599_, 5);
lean_inc_ref(v_congrInfo_2606_);
v_defEqI_2607_ = lean_ctor_get(v___x_2599_, 6);
lean_inc_ref(v_defEqI_2607_);
v_extensions_2608_ = lean_ctor_get(v___x_2599_, 7);
lean_inc_ref(v_extensions_2608_);
v_issues_2609_ = lean_ctor_get(v___x_2599_, 8);
lean_inc(v_issues_2609_);
v_instanceOverrides_2610_ = lean_ctor_get(v___x_2599_, 10);
lean_inc_ref(v_instanceOverrides_2610_);
v_debug_2611_ = lean_ctor_get_uint8(v___x_2599_, sizeof(void*)*11);
lean_dec(v___x_2599_);
v_cache_2612_ = lean_ctor_get(v_canon_2600_, 0);
lean_inc_ref(v_cache_2612_);
v_cacheInType_2613_ = lean_ctor_get(v_canon_2600_, 1);
lean_inc_ref(v_cacheInType_2613_);
lean_dec_ref(v_canon_2600_);
v___x_2614_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2613_, v_e_2312_);
switch(lean_obj_tag(v___x_2614_))
{
case 0:
{
lean_object* v_index_2615_; lean_object* v_size_2616_; lean_object* v___x_2617_; 
v_index_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_index_2615_);
lean_dec_ref_known(v___x_2614_, 3);
v_size_2616_ = lean_ctor_get(v_cacheInType_2613_, 0);
lean_inc(v_size_2616_);
lean_inc(v_a_2598_);
v___x_2617_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_2613_, v_size_2616_, v_index_2615_, v_e_2312_, v_a_2598_);
lean_dec(v_index_2615_);
v___y_2491_ = v_defEqI_2607_;
v___y_2492_ = v_maxFVar_2602_;
v___y_2493_ = v_debug_2611_;
v___y_2494_ = v_issues_2609_;
v___y_2495_ = v_cache_2612_;
v___y_2496_ = v_congrInfo_2606_;
v___y_2497_ = v_proofInstInfo_2603_;
v___y_2498_ = v_inferType_2604_;
v___y_2499_ = v_a_2598_;
v___y_2500_ = v_instanceOverrides_2610_;
v___y_2501_ = v_extensions_2608_;
v___y_2502_ = v_share_2601_;
v___y_2503_ = v_getLevel_2605_;
v___y_2504_ = v___x_2617_;
goto v___jp_2490_;
}
case 1:
{
lean_object* v_index_2618_; lean_object* v_size_2619_; lean_object* v_keyArray_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v_index_2618_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_index_2618_);
lean_dec_ref_known(v___x_2614_, 1);
v_size_2619_ = lean_ctor_get(v_cacheInType_2613_, 0);
v_keyArray_2620_ = lean_ctor_get(v_cacheInType_2613_, 1);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = lean_nat_add(v_size_2619_, v___x_2621_);
v___x_2623_ = lean_array_get_size(v_keyArray_2620_);
v___x_2624_ = lean_nat_dec_lt(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_dec(v___x_2622_);
lean_dec(v_index_2618_);
v___y_2573_ = v_defEqI_2607_;
v___y_2574_ = v_maxFVar_2602_;
v___y_2575_ = v_debug_2611_;
v___y_2576_ = v_cache_2612_;
v___y_2577_ = v_proofInstInfo_2603_;
v___y_2578_ = v_congrInfo_2606_;
v___y_2579_ = v_inferType_2604_;
v___y_2580_ = v_cacheInType_2613_;
v___y_2581_ = v_issues_2609_;
v___y_2582_ = v_a_2598_;
v___y_2583_ = v_instanceOverrides_2610_;
v___y_2584_ = v_extensions_2608_;
v___y_2585_ = v_share_2601_;
v___y_2586_ = v_getLevel_2605_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2625_ = lean_unsigned_to_nat(4u);
v___x_2626_ = lean_nat_mul(v___x_2622_, v___x_2625_);
v___x_2627_ = lean_unsigned_to_nat(3u);
v___x_2628_ = lean_nat_mul(v___x_2623_, v___x_2627_);
v___x_2629_ = lean_nat_dec_le(v___x_2626_, v___x_2628_);
lean_dec(v___x_2628_);
lean_dec(v___x_2626_);
if (v___x_2629_ == 0)
{
lean_dec(v___x_2622_);
lean_dec(v_index_2618_);
v___y_2573_ = v_defEqI_2607_;
v___y_2574_ = v_maxFVar_2602_;
v___y_2575_ = v_debug_2611_;
v___y_2576_ = v_cache_2612_;
v___y_2577_ = v_proofInstInfo_2603_;
v___y_2578_ = v_congrInfo_2606_;
v___y_2579_ = v_inferType_2604_;
v___y_2580_ = v_cacheInType_2613_;
v___y_2581_ = v_issues_2609_;
v___y_2582_ = v_a_2598_;
v___y_2583_ = v_instanceOverrides_2610_;
v___y_2584_ = v_extensions_2608_;
v___y_2585_ = v_share_2601_;
v___y_2586_ = v_getLevel_2605_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2630_; 
lean_inc(v_a_2598_);
v___x_2630_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_2613_, v___x_2622_, v_index_2618_, v_e_2312_, v_a_2598_);
lean_dec(v_index_2618_);
v___y_2491_ = v_defEqI_2607_;
v___y_2492_ = v_maxFVar_2602_;
v___y_2493_ = v_debug_2611_;
v___y_2494_ = v_issues_2609_;
v___y_2495_ = v_cache_2612_;
v___y_2496_ = v_congrInfo_2606_;
v___y_2497_ = v_proofInstInfo_2603_;
v___y_2498_ = v_inferType_2604_;
v___y_2499_ = v_a_2598_;
v___y_2500_ = v_instanceOverrides_2610_;
v___y_2501_ = v_extensions_2608_;
v___y_2502_ = v_share_2601_;
v___y_2503_ = v_getLevel_2605_;
v___y_2504_ = v___x_2630_;
goto v___jp_2490_;
}
}
}
default: 
{
lean_object* v_size_2631_; lean_object* v_keyArray_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_size_2631_ = lean_ctor_get(v_cacheInType_2613_, 0);
v_keyArray_2632_ = lean_ctor_get(v_cacheInType_2613_, 1);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v_size_2631_, v___x_2633_);
v___x_2635_ = lean_array_get_size(v_keyArray_2632_);
v___x_2636_ = lean_nat_dec_lt(v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
lean_dec(v___x_2634_);
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_2613_);
lean_dec_ref(v_cacheInType_2613_);
v___y_2530_ = v_defEqI_2607_;
v___y_2531_ = v_maxFVar_2602_;
v___y_2532_ = v_debug_2611_;
v___y_2533_ = v_cache_2612_;
v___y_2534_ = v_proofInstInfo_2603_;
v___y_2535_ = v_congrInfo_2606_;
v___y_2536_ = v_inferType_2604_;
v___y_2537_ = v_issues_2609_;
v___y_2538_ = v_a_2598_;
v___y_2539_ = v_instanceOverrides_2610_;
v___y_2540_ = v_extensions_2608_;
v___y_2541_ = v_share_2601_;
v___y_2542_ = v_getLevel_2605_;
v___y_2543_ = v___x_2637_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2638_ = lean_unsigned_to_nat(4u);
v___x_2639_ = lean_nat_mul(v___x_2634_, v___x_2638_);
lean_dec(v___x_2634_);
v___x_2640_ = lean_unsigned_to_nat(3u);
v___x_2641_ = lean_nat_mul(v___x_2635_, v___x_2640_);
v___x_2642_ = lean_nat_dec_le(v___x_2639_, v___x_2641_);
lean_dec(v___x_2641_);
lean_dec(v___x_2639_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_2613_);
lean_dec_ref(v_cacheInType_2613_);
v___y_2530_ = v_defEqI_2607_;
v___y_2531_ = v_maxFVar_2602_;
v___y_2532_ = v_debug_2611_;
v___y_2533_ = v_cache_2612_;
v___y_2534_ = v_proofInstInfo_2603_;
v___y_2535_ = v_congrInfo_2606_;
v___y_2536_ = v_inferType_2604_;
v___y_2537_ = v_issues_2609_;
v___y_2538_ = v_a_2598_;
v___y_2539_ = v_instanceOverrides_2610_;
v___y_2540_ = v_extensions_2608_;
v___y_2541_ = v_share_2601_;
v___y_2542_ = v_getLevel_2605_;
v___y_2543_ = v___x_2643_;
goto v___jp_2529_;
}
else
{
v___y_2530_ = v_defEqI_2607_;
v___y_2531_ = v_maxFVar_2602_;
v___y_2532_ = v_debug_2611_;
v___y_2533_ = v_cache_2612_;
v___y_2534_ = v_proofInstInfo_2603_;
v___y_2535_ = v_congrInfo_2606_;
v___y_2536_ = v_inferType_2604_;
v___y_2537_ = v_issues_2609_;
v___y_2538_ = v_a_2598_;
v___y_2539_ = v_instanceOverrides_2610_;
v___y_2540_ = v_extensions_2608_;
v___y_2541_ = v_share_2601_;
v___y_2542_ = v_getLevel_2605_;
v___y_2543_ = v_cacheInType_2613_;
goto v___jp_2529_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2312_);
return v___y_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0(lean_object* v___x_2698_, lean_object* v_a_2699_, lean_object* v___x_2700_, lean_object* v_snd_2701_, uint8_t v___x_2702_, lean_object* v_fst_2703_, lean_object* v_____r_2704_, uint8_t v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_arg_x27_2714_; lean_object* v___x_2726_; 
lean_inc_ref(v___x_2700_);
v___x_2726_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2698_, v_a_2699_, v___x_2700_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; uint8_t v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = lean_unbox(v_a_2727_);
lean_dec(v_a_2727_);
switch(v___x_2728_)
{
case 0:
{
lean_object* v___x_2729_; 
lean_inc_ref(v___x_2700_);
v___x_2729_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2700_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v_arg_x27_2714_ = v_a_2730_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2731_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
case 1:
{
lean_object* v___x_2739_; 
lean_inc_ref(v___x_2700_);
v___x_2739_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2700_, v___y_2709_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; uint8_t v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___x_2759_ = l_Lean_Expr_cleanupAnnotations(v_a_2740_);
v___x_2760_ = l_Lean_Expr_isApp(v___x_2759_);
if (v___x_2760_ == 0)
{
lean_dec_ref(v___x_2759_);
v___y_2742_ = v___y_2705_;
v___y_2743_ = v___y_2706_;
v___y_2744_ = v___y_2707_;
v___y_2745_ = v___y_2708_;
v___y_2746_ = v___y_2709_;
v___y_2747_ = v___y_2710_;
v___y_2748_ = v___y_2711_;
goto v___jp_2741_;
}
else
{
lean_object* v_arg_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_arg_2761_ = lean_ctor_get(v___x_2759_, 1);
lean_inc_ref(v_arg_2761_);
v___x_2762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2759_);
v___x_2763_ = l_Lean_Expr_isApp(v___x_2762_);
if (v___x_2763_ == 0)
{
lean_dec_ref(v___x_2762_);
lean_dec_ref(v_arg_2761_);
v___y_2742_ = v___y_2705_;
v___y_2743_ = v___y_2706_;
v___y_2744_ = v___y_2707_;
v___y_2745_ = v___y_2708_;
v___y_2746_ = v___y_2709_;
v___y_2747_ = v___y_2710_;
v___y_2748_ = v___y_2711_;
goto v___jp_2741_;
}
else
{
lean_object* v_arg_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_arg_2764_ = lean_ctor_get(v___x_2762_, 1);
lean_inc_ref(v_arg_2764_);
v___x_2765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2762_);
v___x_2766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1));
v___x_2767_ = l_Lean_Expr_isConstOf(v___x_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2769_ = l_Lean_Expr_isConstOf(v___x_2765_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_dec_ref(v___x_2765_);
lean_dec_ref(v_arg_2764_);
lean_dec_ref(v_arg_2761_);
v___y_2742_ = v___y_2705_;
v___y_2743_ = v___y_2706_;
v___y_2744_ = v___y_2707_;
v___y_2745_ = v___y_2708_;
v___y_2746_ = v___y_2709_;
v___y_2747_ = v___y_2710_;
v___y_2748_ = v___y_2711_;
goto v___jp_2741_;
}
else
{
lean_object* v___x_2770_; 
lean_inc_ref(v___x_2700_);
v___x_2770_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2765_, v_arg_2764_, v_arg_2761_, v___x_2700_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v_arg_x27_2714_ = v_a_2771_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2772_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2770_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2770_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v___x_2780_; 
lean_inc_ref(v___x_2700_);
v___x_2780_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2765_, v_arg_2764_, v_arg_2761_, v___x_2700_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v_arg_x27_2714_ = v_a_2781_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2782_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2780_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2780_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
v___jp_2741_:
{
lean_object* v___x_2749_; 
lean_inc_ref(v___x_2700_);
v___x_2749_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2700_, v___x_2702_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_arg_x27_2714_ = v_a_2750_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2751_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2749_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2749_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2790_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2739_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2739_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
default: 
{
lean_object* v___x_2798_; 
lean_inc_ref(v___x_2700_);
v___x_2798_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2700_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v_arg_x27_2714_ = v_a_2799_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2800_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2798_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_fst_2703_);
lean_dec(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_a_2808_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2726_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2726_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
v___jp_2713_:
{
size_t v___x_2715_; size_t v___x_2716_; uint8_t v___x_2717_; 
v___x_2715_ = lean_ptr_addr(v___x_2700_);
lean_dec_ref(v___x_2700_);
v___x_2716_ = lean_ptr_addr(v_arg_x27_2714_);
v___x_2717_ = lean_usize_dec_eq(v___x_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v_fst_2703_);
v___x_2718_ = lean_array_fset(v_snd_2701_, v_a_2699_, v_arg_x27_2714_);
v___x_2719_ = lean_box(v___x_2702_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_arg_x27_2714_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_fst_2703_);
lean_ctor_set(v___x_2723_, 1, v_snd_2701_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2820_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_2821_ = l_Lean_Name_append(v___x_2820_, v___x_2819_);
return v___x_2821_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__3));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__5));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__7));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_upperBound_2831_, lean_object* v___x_2832_, lean_object* v_a_2833_, lean_object* v_b_2834_, uint8_t v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___y_2844_; uint8_t v___x_2866_; 
v___x_2866_ = lean_nat_dec_lt(v_a_2833_, v_upperBound_2831_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_a_2833_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2834_);
return v___x_2867_;
}
else
{
lean_object* v_options_2868_; lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2934_; 
v_options_2868_ = lean_ctor_get(v___y_2840_, 2);
v_fst_2869_ = lean_ctor_get(v_b_2834_, 0);
v_snd_2870_ = lean_ctor_get(v_b_2834_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_b_2834_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2872_ = v_b_2834_;
v_isShared_2873_ = v_isSharedCheck_2934_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snd_2870_);
lean_inc(v_fst_2869_);
lean_dec(v_b_2834_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2934_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_inheritedTraceOptions_2874_; uint8_t v_hasTrace_2875_; lean_object* v___x_2876_; 
v_inheritedTraceOptions_2874_ = lean_ctor_get(v___y_2840_, 13);
v_hasTrace_2875_ = lean_ctor_get_uint8(v_options_2868_, sizeof(void*)*1);
v___x_2876_ = lean_array_fget(v_snd_2870_, v_a_2833_);
if (v_hasTrace_2875_ == 0)
{
lean_del_object(v___x_2872_);
goto v___jp_2877_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2881_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2);
v___x_2882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2874_, v_options_2868_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_del_object(v___x_2872_);
goto v___jp_2877_;
}
else
{
lean_object* v___x_2883_; 
lean_inc(v___x_2876_);
v___x_2883_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2832_, v_a_2833_, v___x_2876_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
lean_inc(v___y_2841_);
lean_inc_ref(v___y_2840_);
lean_inc(v___y_2839_);
lean_inc_ref(v___y_2838_);
lean_inc(v___x_2876_);
v___x_2885_ = lean_infer_type(v___x_2876_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___y_2889_; uint8_t v___x_2913_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__4);
v___x_2913_ = lean_unbox(v_a_2884_);
lean_dec(v_a_2884_);
switch(v___x_2913_)
{
case 0:
{
lean_object* v___x_2914_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2889_ = v___x_2914_;
goto v___jp_2888_;
}
case 1:
{
lean_object* v___x_2915_; 
v___x_2915_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2889_ = v___x_2915_;
goto v___jp_2888_;
}
case 2:
{
lean_object* v___x_2916_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2889_ = v___x_2916_;
goto v___jp_2888_;
}
default: 
{
lean_object* v___x_2917_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2889_ = v___x_2917_;
goto v___jp_2888_;
}
}
v___jp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_inc(v___y_2889_);
v___x_2890_ = l_Lean_MessageData_ofFormat(v___y_2889_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 7);
lean_ctor_set(v___x_2872_, 1, v___x_2890_);
lean_ctor_set(v___x_2872_, 0, v___x_2887_);
v___x_2892_ = v___x_2872_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2893_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__6);
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
lean_inc(v___x_2876_);
v___x_2895_ = l_Lean_MessageData_ofExpr(v___x_2876_);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__8);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_MessageData_ofExpr(v_a_2886_);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2880_, v___x_2900_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0(v___x_2832_, v_a_2833_, v___x_2876_, v_snd_2870_, v___x_2866_, v_fst_2869_, v_a_2902_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
v___y_2844_ = v___x_2903_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v___x_2876_);
lean_dec(v_snd_2870_);
lean_dec(v_fst_2869_);
lean_dec(v_a_2833_);
v_a_2904_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2901_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2901_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_a_2884_);
lean_dec(v___x_2876_);
lean_del_object(v___x_2872_);
lean_dec(v_snd_2870_);
lean_dec(v_fst_2869_);
lean_dec(v_a_2833_);
v_a_2918_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2885_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2885_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v___x_2876_);
lean_del_object(v___x_2872_);
lean_dec(v_snd_2870_);
lean_dec(v_fst_2869_);
lean_dec(v_a_2833_);
v_a_2926_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2883_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2883_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
v___jp_2877_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0(v___x_2832_, v_a_2833_, v___x_2876_, v_snd_2870_, v___x_2866_, v_fst_2869_, v___x_2878_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
v___y_2844_ = v___x_2879_;
goto v___jp_2843_;
}
}
}
v___jp_2843_:
{
if (lean_obj_tag(v___y_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2857_; 
v_a_2845_ = lean_ctor_get(v___y_2844_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___y_2844_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2847_ = v___y_2844_;
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___y_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
if (lean_obj_tag(v_a_2845_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; 
lean_dec(v_a_2833_);
v_a_2849_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v_a_2845_, 1);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_a_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2847_);
v_a_2853_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v_a_2845_, 1);
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_add(v_a_2833_, v___x_2854_);
lean_dec(v_a_2833_);
v_a_2833_ = v___x_2855_;
v_b_2834_ = v_a_2853_;
goto _start;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2833_);
v_a_2858_ = lean_ctor_get(v___y_2844_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___y_2844_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___y_2844_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___y_2844_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_e_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_, uint8_t v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___y_2948_; uint8_t v_modified_2949_; lean_object* v_f_2950_; uint8_t v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v_args_3006_; uint8_t v_modified_3007_; uint8_t v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; uint8_t v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; 
if (lean_obj_tag(v_x_2936_) == 5)
{
lean_object* v_fn_3043_; lean_object* v_arg_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_fn_3043_ = lean_ctor_get(v_x_2936_, 0);
lean_inc_ref(v_fn_3043_);
v_arg_3044_ = lean_ctor_get(v_x_2936_, 1);
lean_inc_ref(v_arg_3044_);
lean_dec_ref_known(v_x_2936_, 2);
v___x_3045_ = lean_array_set(v_x_2937_, v_x_2938_, v_arg_3044_);
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_nat_sub(v_x_2938_, v___x_3046_);
lean_dec(v_x_2938_);
v_x_2936_ = v_fn_3043_;
v_x_2937_ = v___x_3045_;
v_x_2938_ = v___x_3047_;
goto _start;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
lean_dec(v_x_2938_);
v___x_3049_ = lean_array_get_size(v_x_2937_);
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = lean_nat_dec_eq(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
v___y_3022_ = v___y_2939_;
v___y_3023_ = v___y_2940_;
v___y_3024_ = v___y_2941_;
v___y_3025_ = v___y_2942_;
v___y_3026_ = v___y_2943_;
v___y_3027_ = v___y_2944_;
v___y_3028_ = v___y_2945_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___closed__1));
v___x_3053_ = l_Lean_Expr_isConstOf(v_x_2936_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_3055_ = l_Lean_Expr_isConstOf(v_x_2936_, v___x_3054_);
if (v___x_3055_ == 0)
{
v___y_3022_ = v___y_2939_;
v___y_3023_ = v___y_2940_;
v___y_3024_ = v___y_2941_;
v___y_3025_ = v___y_2942_;
v___y_3026_ = v___y_2943_;
v___y_3027_ = v___y_2944_;
v___y_3028_ = v___y_2945_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3056_ = l_Lean_instInhabitedExpr;
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_array_get(v___x_3056_, v_x_2937_, v___x_3057_);
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_array_get(v___x_3056_, v_x_2937_, v___x_3059_);
lean_dec_ref(v_x_2937_);
v___x_3061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2936_, v___x_3058_, v___x_3060_, v_e_2935_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
return v___x_3061_;
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_prop_3064_; lean_object* v___x_3065_; 
v___x_3062_ = l_Lean_instInhabitedExpr;
v___x_3063_ = lean_unsigned_to_nat(0u);
v_prop_3064_ = lean_array_get_borrowed(v___x_3062_, v_x_2937_, v___x_3063_);
lean_inc(v_prop_3064_);
v___x_3065_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_3064_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3082_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
size_t v___x_3070_; size_t v___x_3071_; uint8_t v___x_3072_; 
v___x_3070_ = lean_ptr_addr(v_prop_3064_);
v___x_3071_ = lean_ptr_addr(v_a_3066_);
v___x_3072_ = lean_usize_dec_eq(v___x_3070_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_dec_ref(v_e_2935_);
v___x_3073_ = lean_unsigned_to_nat(1u);
v___x_3074_ = lean_array_get(v___x_3062_, v_x_2937_, v___x_3073_);
lean_dec_ref(v_x_2937_);
v___x_3075_ = l_Lean_mkAppB(v_x_2936_, v_a_3066_, v___x_3074_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3075_);
v___x_3077_ = v___x_3068_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
else
{
lean_object* v___x_3080_; 
lean_dec(v_a_3066_);
lean_dec_ref(v_x_2937_);
lean_dec_ref(v_x_2936_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v_e_2935_);
v___x_3080_ = v___x_3068_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_e_2935_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_dec_ref(v_x_2937_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_e_2935_);
return v___x_3065_;
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_box(0);
lean_inc_ref(v_f_2950_);
v___x_2959_ = l_Lean_Meta_getFunInfo(v_f_2950_, v___x_2958_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v_paramInfo_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2995_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v_paramInfo_2961_ = lean_ctor_get(v_a_2960_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v_a_2960_, 1);
lean_dec(v_unused_2996_);
v___x_2963_ = v_a_2960_;
v_isShared_2964_ = v_isSharedCheck_2995_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_paramInfo_2961_);
lean_dec(v_a_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2995_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2965_ = lean_array_get_size(v___y_2948_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_box(v_modified_2949_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___y_2948_);
lean_ctor_set(v___x_2963_, 0, v___x_2967_);
v___x_2969_ = v___x_2963_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___y_2948_);
v___x_2969_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2965_, v_paramInfo_2961_, v___x_2966_, v___x_2969_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec_ref(v_paramInfo_2961_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2985_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2985_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2985_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_fst_2975_; uint8_t v___x_2976_; 
v_fst_2975_ = lean_ctor_get(v_a_2971_, 0);
v___x_2976_ = lean_unbox(v_fst_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_a_2971_);
lean_dec_ref(v_f_2950_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v_e_2935_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_e_2935_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
else
{
lean_object* v_snd_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_dec_ref(v_e_2935_);
v_snd_2980_ = lean_ctor_get(v_a_2971_, 1);
lean_inc(v_snd_2980_);
lean_dec(v_a_2971_);
v___x_2981_ = l_Lean_mkAppN(v_f_2950_, v_snd_2980_);
lean_dec(v_snd_2980_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2981_);
v___x_2983_ = v___x_2973_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec_ref(v_f_2950_);
lean_dec_ref(v_e_2935_);
v_a_2986_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2970_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2970_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v_f_2950_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v_e_2935_);
v_a_2997_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2959_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2959_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
v___jp_3005_:
{
lean_object* v___x_3015_; 
lean_inc_ref(v_x_2936_);
v___x_3015_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2936_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; size_t v___x_3017_; size_t v___x_3018_; uint8_t v___x_3019_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_ptr_addr(v_x_2936_);
v___x_3018_ = lean_ptr_addr(v_a_3016_);
v___x_3019_ = lean_usize_dec_eq(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
lean_dec_ref(v_x_2936_);
v___x_3020_ = 1;
v___y_2948_ = v_args_3006_;
v_modified_2949_ = v___x_3020_;
v_f_2950_ = v_a_3016_;
v___y_2951_ = v___y_3008_;
v___y_2952_ = v___y_3009_;
v___y_2953_ = v___y_3010_;
v___y_2954_ = v___y_3011_;
v___y_2955_ = v___y_3012_;
v___y_2956_ = v___y_3013_;
v___y_2957_ = v___y_3014_;
goto v___jp_2947_;
}
else
{
lean_dec(v_a_3016_);
v___y_2948_ = v_args_3006_;
v_modified_2949_ = v_modified_3007_;
v_f_2950_ = v_x_2936_;
v___y_2951_ = v___y_3008_;
v___y_2952_ = v___y_3009_;
v___y_2953_ = v___y_3010_;
v___y_2954_ = v___y_3011_;
v___y_2955_ = v___y_3012_;
v___y_2956_ = v___y_3013_;
v___y_2957_ = v___y_3014_;
goto v___jp_2947_;
}
}
else
{
lean_dec_ref(v_args_3006_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_e_2935_);
return v___x_3015_;
}
}
v___jp_3021_:
{
uint8_t v_modified_3029_; lean_object* v___x_3030_; uint8_t v_modified_3031_; 
v_modified_3029_ = 0;
v___x_3030_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_3031_ = l_Lean_Expr_isConstOf(v_x_2936_, v___x_3030_);
if (v_modified_3031_ == 0)
{
v_args_3006_ = v_x_2937_;
v_modified_3007_ = v_modified_3029_;
v___y_3008_ = v___y_3022_;
v___y_3009_ = v___y_3023_;
v___y_3010_ = v___y_3024_;
v___y_3011_ = v___y_3025_;
v___y_3012_ = v___y_3026_;
v___y_3013_ = v___y_3027_;
v___y_3014_ = v___y_3028_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3032_; 
lean_inc_ref(v_x_2937_);
v___x_3032_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2937_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
if (lean_obj_tag(v_a_3033_) == 1)
{
lean_object* v_val_3034_; 
lean_dec_ref(v_x_2937_);
v_val_3034_ = lean_ctor_get(v_a_3033_, 0);
lean_inc(v_val_3034_);
lean_dec_ref_known(v_a_3033_, 1);
v_args_3006_ = v_val_3034_;
v_modified_3007_ = v_modified_3031_;
v___y_3008_ = v___y_3022_;
v___y_3009_ = v___y_3023_;
v___y_3010_ = v___y_3024_;
v___y_3011_ = v___y_3025_;
v___y_3012_ = v___y_3026_;
v___y_3013_ = v___y_3027_;
v___y_3014_ = v___y_3028_;
goto v___jp_3005_;
}
else
{
lean_dec(v_a_3033_);
v_args_3006_ = v_x_2937_;
v_modified_3007_ = v_modified_3029_;
v___y_3008_ = v___y_3022_;
v___y_3009_ = v___y_3023_;
v___y_3010_ = v___y_3024_;
v___y_3011_ = v___y_3025_;
v___y_3012_ = v___y_3026_;
v___y_3013_ = v___y_3027_;
v___y_3014_ = v___y_3028_;
goto v___jp_3005_;
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v_x_2937_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_e_2935_);
v_a_3035_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3032_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3032_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_3083_, uint8_t v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_dummy_3092_; lean_object* v_nargs_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_dummy_3092_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_3093_ = l_Lean_Expr_getAppNumArgs(v_e_3083_);
lean_inc(v_nargs_3093_);
v___x_3094_ = lean_mk_array(v_nargs_3093_, v_dummy_3092_);
v___x_3095_ = lean_unsigned_to_nat(1u);
v___x_3096_ = lean_nat_sub(v_nargs_3093_, v___x_3095_);
lean_dec(v_nargs_3093_);
lean_inc_ref(v_e_3083_);
v___x_3097_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_e_3083_, v_e_3083_, v___x_3094_, v___x_3096_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_3098_, uint8_t v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3109_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_3108_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
return v___x_3109_;
}
else
{
return v___x_3107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_3110_, uint8_t v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_Meta_reduceMatcher_x3f(v_e_3110_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
if (lean_obj_tag(v_a_3120_) == 0)
{
lean_object* v_val_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v_e_3110_);
v_val_3121_ = lean_ctor_get(v_a_3120_, 0);
lean_inc_ref(v_val_3121_);
lean_dec_ref_known(v_a_3120_, 1);
v___x_3122_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_3121_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; 
lean_dec(v_a_3120_);
v___x_3123_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = l_Lean_Meta_reduceMatcher_x3f(v_a_3124_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3135_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3135_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3135_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
if (lean_obj_tag(v_a_3126_) == 0)
{
lean_object* v_val_3130_; lean_object* v___x_3131_; 
lean_del_object(v___x_3128_);
lean_dec(v_a_3124_);
v_val_3130_ = lean_ctor_get(v_a_3126_, 0);
lean_inc_ref(v_val_3130_);
lean_dec_ref_known(v_a_3126_, 1);
v___x_3131_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_3130_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3131_;
}
else
{
lean_object* v___x_3133_; 
lean_dec(v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v_a_3124_);
v___x_3133_ = v___x_3128_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3124_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3124_);
v_a_3136_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3125_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3125_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
return v___x_3123_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v_e_3110_);
v_a_3144_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3119_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3119_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_3158_, uint8_t v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v___x_3167_; 
lean_inc_ref(v_e_3158_);
v___x_3167_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3158_, v_a_3163_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; uint8_t v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3179_ = l_Lean_Expr_cleanupAnnotations(v_a_3168_);
v___x_3180_ = l_Lean_Expr_isApp(v___x_3179_);
if (v___x_3180_ == 0)
{
lean_dec_ref(v___x_3179_);
v___y_3170_ = v_a_3159_;
v___y_3171_ = v_a_3160_;
v___y_3172_ = v_a_3161_;
v___y_3173_ = v_a_3162_;
v___y_3174_ = v_a_3163_;
v___y_3175_ = v_a_3164_;
v___y_3176_ = v_a_3165_;
goto v___jp_3169_;
}
else
{
lean_object* v_arg_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_arg_3181_ = lean_ctor_get(v___x_3179_, 1);
lean_inc_ref(v_arg_3181_);
v___x_3182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3179_);
v___x_3183_ = l_Lean_Expr_isApp(v___x_3182_);
if (v___x_3183_ == 0)
{
lean_dec_ref(v___x_3182_);
lean_dec_ref(v_arg_3181_);
v___y_3170_ = v_a_3159_;
v___y_3171_ = v_a_3160_;
v___y_3172_ = v_a_3161_;
v___y_3173_ = v_a_3162_;
v___y_3174_ = v_a_3163_;
v___y_3175_ = v_a_3164_;
v___y_3176_ = v_a_3165_;
goto v___jp_3169_;
}
else
{
lean_object* v_arg_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v_arg_3184_ = lean_ctor_get(v___x_3182_, 1);
lean_inc_ref(v_arg_3184_);
v___x_3185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3182_);
v___x_3186_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_3187_ = l_Lean_Expr_isConstOf(v___x_3185_, v___x_3186_);
if (v___x_3187_ == 0)
{
lean_dec_ref(v___x_3185_);
lean_dec_ref(v_arg_3184_);
lean_dec_ref(v_arg_3181_);
v___y_3170_ = v_a_3159_;
v___y_3171_ = v_a_3160_;
v___y_3172_ = v_a_3161_;
v___y_3173_ = v_a_3162_;
v___y_3174_ = v_a_3163_;
v___y_3175_ = v_a_3164_;
v___y_3176_ = v_a_3165_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_3185_, v_arg_3184_, v_arg_3181_, v_e_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3188_;
}
}
}
v___jp_3169_:
{
uint8_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = 0;
v___x_3178_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3158_, v___x_3177_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
}
else
{
lean_dec_ref(v_e_3158_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_3189_, lean_object* v_00_u03b1_3190_, lean_object* v_c_3191_, lean_object* v_inst_3192_, lean_object* v_a_3193_, lean_object* v_b_3194_, uint8_t v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_3191_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; uint8_t v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc_n(v_a_3204_, 2);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_3204_);
if (v___x_3205_ == 0)
{
uint8_t v___x_3206_; 
lean_inc(v_a_3204_);
v___x_3206_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_3204_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_3190_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3209_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_3192_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3193_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = l_Lean_mkApp5(v_f_3189_, v_a_3208_, v_a_3204_, v_a_3210_, v_a_3212_, v_a_3214_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3218_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
else
{
lean_dec(v_a_3212_);
lean_dec(v_a_3210_);
lean_dec(v_a_3208_);
lean_dec(v_a_3204_);
lean_dec_ref(v_f_3189_);
return v___x_3213_;
}
}
else
{
lean_dec(v_a_3210_);
lean_dec(v_a_3208_);
lean_dec(v_a_3204_);
lean_dec_ref(v_b_3194_);
lean_dec_ref(v_f_3189_);
return v___x_3211_;
}
}
else
{
lean_dec(v_a_3208_);
lean_dec(v_a_3204_);
lean_dec_ref(v_b_3194_);
lean_dec_ref(v_a_3193_);
lean_dec_ref(v_f_3189_);
return v___x_3209_;
}
}
else
{
lean_dec(v_a_3204_);
lean_dec_ref(v_b_3194_);
lean_dec_ref(v_a_3193_);
lean_dec_ref(v_inst_3192_);
lean_dec_ref(v_f_3189_);
return v___x_3207_;
}
}
else
{
lean_object* v___x_3223_; 
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3193_);
lean_dec_ref(v_inst_3192_);
lean_dec_ref(v_00_u03b1_3190_);
lean_dec_ref(v_f_3189_);
v___x_3223_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3223_;
}
}
else
{
lean_object* v___x_3224_; 
lean_dec(v_a_3204_);
lean_dec_ref(v_b_3194_);
lean_dec_ref(v_inst_3192_);
lean_dec_ref(v_00_u03b1_3190_);
lean_dec_ref(v_f_3189_);
v___x_3224_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3193_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3224_;
}
}
else
{
lean_dec_ref(v_b_3194_);
lean_dec_ref(v_a_3193_);
lean_dec_ref(v_inst_3192_);
lean_dec_ref(v_00_u03b1_3190_);
lean_dec_ref(v_f_3189_);
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_3225_, lean_object* v_00_u03b1_3226_, lean_object* v_c_3227_, lean_object* v_a_3228_, lean_object* v_b_3229_, uint8_t v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_3227_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; uint8_t v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc_n(v_a_3239_, 2);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = l_Lean_Expr_isBoolTrue(v_a_3239_);
if (v___x_3240_ == 0)
{
uint8_t v___x_3241_; 
lean_inc(v_a_3239_);
v___x_3241_ = l_Lean_Expr_isBoolFalse(v_a_3239_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_3226_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3228_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3255_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = l_Lean_mkApp4(v_f_3225_, v_a_3243_, v_a_3239_, v_a_3245_, v_a_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
else
{
lean_dec(v_a_3245_);
lean_dec(v_a_3243_);
lean_dec(v_a_3239_);
lean_dec_ref(v_f_3225_);
return v___x_3246_;
}
}
else
{
lean_dec(v_a_3243_);
lean_dec(v_a_3239_);
lean_dec_ref(v_b_3229_);
lean_dec_ref(v_f_3225_);
return v___x_3244_;
}
}
else
{
lean_dec(v_a_3239_);
lean_dec_ref(v_b_3229_);
lean_dec_ref(v_a_3228_);
lean_dec_ref(v_f_3225_);
return v___x_3242_;
}
}
else
{
lean_object* v___x_3256_; 
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3228_);
lean_dec_ref(v_00_u03b1_3226_);
lean_dec_ref(v_f_3225_);
v___x_3256_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
return v___x_3256_;
}
}
else
{
lean_object* v___x_3257_; 
lean_dec(v_a_3239_);
lean_dec_ref(v_b_3229_);
lean_dec_ref(v_00_u03b1_3226_);
lean_dec_ref(v_f_3225_);
v___x_3257_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3228_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
return v___x_3257_;
}
}
else
{
lean_dec_ref(v_b_3229_);
lean_dec_ref(v_a_3228_);
lean_dec_ref(v_00_u03b1_3226_);
lean_dec_ref(v_f_3225_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_3258_, uint8_t v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; uint8_t v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___x_3294_; 
lean_inc_ref(v_e_3258_);
v___x_3294_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3258_, v_a_3263_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3306_ = l_Lean_Expr_cleanupAnnotations(v_a_3295_);
v___x_3307_ = l_Lean_Expr_isApp(v___x_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v___x_3306_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v_arg_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v_arg_3308_ = lean_ctor_get(v___x_3306_, 1);
lean_inc_ref(v_arg_3308_);
v___x_3309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3306_);
v___x_3310_ = l_Lean_Expr_isApp(v___x_3309_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v___x_3309_);
lean_dec_ref(v_arg_3308_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v_arg_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v_arg_3311_ = lean_ctor_get(v___x_3309_, 1);
lean_inc_ref(v_arg_3311_);
v___x_3312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3309_);
v___x_3313_ = l_Lean_Expr_isApp(v___x_3312_);
if (v___x_3313_ == 0)
{
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3308_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v_arg_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_arg_3314_ = lean_ctor_get(v___x_3312_, 1);
lean_inc_ref(v_arg_3314_);
v___x_3315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3312_);
v___x_3316_ = l_Lean_Expr_isApp(v___x_3315_);
if (v___x_3316_ == 0)
{
lean_dec_ref(v___x_3315_);
lean_dec_ref(v_arg_3314_);
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3308_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v_arg_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_arg_3317_ = lean_ctor_get(v___x_3315_, 1);
lean_inc_ref(v_arg_3317_);
v___x_3318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3315_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3320_ = l_Lean_Expr_isConstOf(v___x_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
uint8_t v___x_3321_; 
v___x_3321_ = l_Lean_Expr_isApp(v___x_3318_);
if (v___x_3321_ == 0)
{
lean_dec_ref(v___x_3318_);
lean_dec_ref(v_arg_3317_);
lean_dec_ref(v_arg_3314_);
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3308_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v_arg_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v_arg_3322_ = lean_ctor_get(v___x_3318_, 1);
lean_inc_ref(v_arg_3322_);
v___x_3323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3318_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3325_ = l_Lean_Expr_isConstOf(v___x_3323_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_dec_ref(v___x_3323_);
lean_dec_ref(v_arg_3322_);
lean_dec_ref(v_arg_3317_);
lean_dec_ref(v_arg_3314_);
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3308_);
v___y_3297_ = v_a_3259_;
v___y_3298_ = v_a_3260_;
v___y_3299_ = v_a_3261_;
v___y_3300_ = v_a_3262_;
v___y_3301_ = v_a_3263_;
v___y_3302_ = v_a_3264_;
v___y_3303_ = v_a_3265_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3326_; 
lean_dec_ref(v_e_3258_);
v___x_3326_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3323_, v_arg_3322_, v_arg_3317_, v_arg_3314_, v_arg_3311_, v_arg_3308_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
return v___x_3326_;
}
}
}
else
{
lean_object* v___x_3327_; 
lean_dec_ref(v_e_3258_);
v___x_3327_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3318_, v_arg_3317_, v_arg_3314_, v_arg_3311_, v_arg_3308_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
return v___x_3327_;
}
}
}
}
}
v___jp_3296_:
{
lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = l_Lean_Expr_getAppFn(v_e_3258_);
v___x_3305_ = l_Lean_Expr_isLambda(v___x_3304_);
if (v___x_3305_ == 0)
{
v___y_3268_ = v___x_3304_;
v___y_3269_ = v___y_3298_;
v___y_3270_ = v___y_3301_;
v___y_3271_ = v___y_3302_;
v___y_3272_ = v___y_3303_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___y_3300_;
v___y_3275_ = v___y_3299_;
v___y_3276_ = v___x_3305_;
goto v___jp_3267_;
}
else
{
v___y_3268_ = v___x_3304_;
v___y_3269_ = v___y_3298_;
v___y_3270_ = v___y_3301_;
v___y_3271_ = v___y_3302_;
v___y_3272_ = v___y_3303_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___y_3300_;
v___y_3275_ = v___y_3299_;
v___y_3276_ = v___y_3297_;
goto v___jp_3267_;
}
}
}
else
{
lean_dec_ref(v_e_3258_);
return v___x_3294_;
}
v___jp_3267_:
{
if (v___y_3276_ == 0)
{
if (lean_obj_tag(v___y_3268_) == 4)
{
lean_object* v_declName_3277_; lean_object* v___x_3278_; 
v_declName_3277_ = lean_ctor_get(v___y_3268_, 0);
lean_inc(v_declName_3277_);
lean_dec_ref_known(v___y_3268_, 2);
v___x_3278_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg(v_declName_3277_, v___y_3272_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; uint8_t v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_unbox(v_a_3279_);
lean_dec(v_a_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3258_, v___y_3273_, v___y_3269_, v___y_3275_, v___y_3274_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3258_, v___y_3273_, v___y_3269_, v___y_3275_, v___y_3274_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3282_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_e_3258_);
v_a_3283_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3278_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3278_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v___x_3291_; 
lean_dec_ref(v___y_3268_);
v___x_3291_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3258_, v___y_3273_, v___y_3269_, v___y_3275_, v___y_3274_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3291_;
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec_ref(v___y_3268_);
v___x_3292_ = l_Lean_Expr_headBeta(v_e_3258_);
v___x_3293_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3292_, v___y_3273_, v___y_3269_, v___y_3275_, v___y_3274_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3293_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3332_ = lean_unsigned_to_nat(18u);
v___x_3333_ = lean_unsigned_to_nat(1896u);
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3336_ = l_mkPanicMessageWithDecl(v___x_3335_, v___x_3334_, v___x_3333_, v___x_3332_, v___x_3331_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3337_, uint8_t v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = l_Lean_Expr_projExpr_x21(v_e_3337_);
v___x_3347_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3346_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___y_3350_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
if (lean_obj_tag(v_e_3337_) == 11)
{
lean_object* v_typeName_3372_; lean_object* v_idx_3373_; lean_object* v_struct_3374_; size_t v___x_3375_; size_t v___x_3376_; uint8_t v___x_3377_; 
v_typeName_3372_ = lean_ctor_get(v_e_3337_, 0);
v_idx_3373_ = lean_ctor_get(v_e_3337_, 1);
v_struct_3374_ = lean_ctor_get(v_e_3337_, 2);
v___x_3375_ = lean_ptr_addr(v_struct_3374_);
v___x_3376_ = lean_ptr_addr(v_a_3348_);
v___x_3377_ = lean_usize_dec_eq(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
lean_inc(v_idx_3373_);
lean_inc(v_typeName_3372_);
lean_dec_ref_known(v_e_3337_, 3);
v___x_3378_ = l_Lean_Expr_proj___override(v_typeName_3372_, v_idx_3373_, v_a_3348_);
v___y_3350_ = v___x_3378_;
goto v___jp_3349_;
}
else
{
lean_dec(v_a_3348_);
v___y_3350_ = v_e_3337_;
goto v___jp_3349_;
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec(v_a_3348_);
lean_dec_ref(v_e_3337_);
v___x_3379_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3380_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__5(v___x_3379_);
v___y_3350_ = v___x_3380_;
goto v___jp_3349_;
}
v___jp_3349_:
{
lean_object* v___x_3351_; 
lean_inc_ref(v___y_3350_);
v___x_3351_ = l_Lean_Meta_reduceProj_x3f(v___y_3350_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3363_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3363_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3363_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
if (lean_obj_tag(v_a_3352_) == 0)
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___y_3350_);
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___y_3350_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; 
lean_dec_ref(v___y_3350_);
v_val_3359_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v_a_3352_, 1);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_val_3359_);
v___x_3361_ = v___x_3354_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_val_3359_);
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
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___y_3350_);
v_a_3364_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3351_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3351_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3337_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3381_, uint8_t v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
switch(lean_obj_tag(v_e_3381_))
{
case 7:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3382_ == 0)
{
lean_object* v___x_3392_; lean_object* v_canon_3393_; lean_object* v_cache_3394_; lean_object* v___x_3395_; 
v___x_3392_ = lean_st_ref_get(v_a_3384_);
v_canon_3393_ = lean_ctor_get(v___x_3392_, 9);
lean_inc_ref(v_canon_3393_);
lean_dec(v___x_3392_);
v_cache_3394_ = lean_ctor_get(v_canon_3393_, 0);
lean_inc_ref(v_cache_3394_);
lean_dec_ref(v_canon_3393_);
v___x_3395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3394_, v_e_3381_);
lean_dec_ref(v_cache_3394_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_val_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 0);
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_val_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v___x_3404_; 
lean_dec(v___x_3395_);
lean_inc_ref(v_e_3381_);
v___x_3404_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3391_, v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3506_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3506_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3506_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v_canon_3410_; lean_object* v_share_3411_; lean_object* v_maxFVar_3412_; lean_object* v_proofInstInfo_3413_; lean_object* v_inferType_3414_; lean_object* v_getLevel_3415_; lean_object* v_congrInfo_3416_; lean_object* v_defEqI_3417_; lean_object* v_extensions_3418_; lean_object* v_issues_3419_; lean_object* v_instanceOverrides_3420_; uint8_t v_debug_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3505_; 
v___x_3409_ = lean_st_ref_take(v_a_3384_);
v_canon_3410_ = lean_ctor_get(v___x_3409_, 9);
v_share_3411_ = lean_ctor_get(v___x_3409_, 0);
v_maxFVar_3412_ = lean_ctor_get(v___x_3409_, 1);
v_proofInstInfo_3413_ = lean_ctor_get(v___x_3409_, 2);
v_inferType_3414_ = lean_ctor_get(v___x_3409_, 3);
v_getLevel_3415_ = lean_ctor_get(v___x_3409_, 4);
v_congrInfo_3416_ = lean_ctor_get(v___x_3409_, 5);
v_defEqI_3417_ = lean_ctor_get(v___x_3409_, 6);
v_extensions_3418_ = lean_ctor_get(v___x_3409_, 7);
v_issues_3419_ = lean_ctor_get(v___x_3409_, 8);
v_instanceOverrides_3420_ = lean_ctor_get(v___x_3409_, 10);
v_debug_3421_ = lean_ctor_get_uint8(v___x_3409_, sizeof(void*)*11);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3423_ = v___x_3409_;
v_isShared_3424_ = v_isSharedCheck_3505_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_instanceOverrides_3420_);
lean_inc(v_canon_3410_);
lean_inc(v_issues_3419_);
lean_inc(v_extensions_3418_);
lean_inc(v_defEqI_3417_);
lean_inc(v_congrInfo_3416_);
lean_inc(v_getLevel_3415_);
lean_inc(v_inferType_3414_);
lean_inc(v_proofInstInfo_3413_);
lean_inc(v_maxFVar_3412_);
lean_inc(v_share_3411_);
lean_dec(v___x_3409_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3505_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_cache_3425_; lean_object* v_cacheInType_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3504_; 
v_cache_3425_ = lean_ctor_get(v_canon_3410_, 0);
v_cacheInType_3426_ = lean_ctor_get(v_canon_3410_, 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_canon_3410_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3428_ = v_canon_3410_;
v_isShared_3429_ = v_isSharedCheck_3504_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_cacheInType_3426_);
lean_inc(v_cache_3425_);
lean_dec(v_canon_3410_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3504_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___y_3431_; lean_object* v___y_3443_; lean_object* v_i_3444_; lean_object* v___y_3450_; lean_object* v___y_3459_; lean_object* v_i_3460_; lean_object* v___x_3474_; 
v___x_3474_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3425_, v_e_3381_);
switch(lean_obj_tag(v___x_3474_))
{
case 0:
{
lean_object* v_index_3475_; lean_object* v_size_3476_; lean_object* v___x_3477_; 
v_index_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_index_3475_);
lean_dec_ref_known(v___x_3474_, 3);
v_size_3476_ = lean_ctor_get(v_cache_3425_, 0);
lean_inc(v_size_3476_);
lean_inc(v_a_3405_);
v___x_3477_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3425_, v_size_3476_, v_index_3475_, v_e_3381_, v_a_3405_);
lean_dec(v_index_3475_);
v___y_3431_ = v___x_3477_;
goto v___jp_3430_;
}
case 1:
{
lean_object* v_index_3478_; lean_object* v_size_3479_; lean_object* v_keyArray_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_index_3478_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_index_3478_);
lean_dec_ref_known(v___x_3474_, 1);
v_size_3479_ = lean_ctor_get(v_cache_3425_, 0);
v_keyArray_3480_ = lean_ctor_get(v_cache_3425_, 1);
v___x_3481_ = lean_unsigned_to_nat(1u);
v___x_3482_ = lean_nat_add(v_size_3479_, v___x_3481_);
v___x_3483_ = lean_array_get_size(v_keyArray_3480_);
v___x_3484_ = lean_nat_dec_lt(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_dec(v___x_3482_);
lean_dec(v_index_3478_);
goto v___jp_3465_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3485_ = lean_unsigned_to_nat(4u);
v___x_3486_ = lean_nat_mul(v___x_3482_, v___x_3485_);
v___x_3487_ = lean_unsigned_to_nat(3u);
v___x_3488_ = lean_nat_mul(v___x_3483_, v___x_3487_);
v___x_3489_ = lean_nat_dec_le(v___x_3486_, v___x_3488_);
lean_dec(v___x_3488_);
lean_dec(v___x_3486_);
if (v___x_3489_ == 0)
{
lean_dec(v___x_3482_);
lean_dec(v_index_3478_);
goto v___jp_3465_;
}
else
{
lean_object* v___x_3490_; 
lean_inc(v_a_3405_);
v___x_3490_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3425_, v___x_3482_, v_index_3478_, v_e_3381_, v_a_3405_);
lean_dec(v_index_3478_);
v___y_3431_ = v___x_3490_;
goto v___jp_3430_;
}
}
}
default: 
{
lean_object* v_size_3491_; lean_object* v_keyArray_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v_size_3491_ = lean_ctor_get(v_cache_3425_, 0);
v_keyArray_3492_ = lean_ctor_get(v_cache_3425_, 1);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_add(v_size_3491_, v___x_3493_);
v___x_3495_ = lean_array_get_size(v_keyArray_3492_);
v___x_3496_ = lean_nat_dec_lt(v___x_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v___x_3494_);
v___x_3497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3425_);
lean_dec_ref(v_cache_3425_);
v___y_3450_ = v___x_3497_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3498_ = lean_unsigned_to_nat(4u);
v___x_3499_ = lean_nat_mul(v___x_3494_, v___x_3498_);
lean_dec(v___x_3494_);
v___x_3500_ = lean_unsigned_to_nat(3u);
v___x_3501_ = lean_nat_mul(v___x_3495_, v___x_3500_);
v___x_3502_ = lean_nat_dec_le(v___x_3499_, v___x_3501_);
lean_dec(v___x_3501_);
lean_dec(v___x_3499_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3425_);
lean_dec_ref(v_cache_3425_);
v___y_3450_ = v___x_3503_;
goto v___jp_3449_;
}
else
{
v___y_3450_ = v_cache_3425_;
goto v___jp_3449_;
}
}
}
}
v___jp_3430_:
{
lean_object* v___x_3433_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___y_3431_);
v___x_3433_ = v___x_3428_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___y_3431_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_cacheInType_3426_);
v___x_3433_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 9, v___x_3433_);
v___x_3435_ = v___x_3423_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_share_3411_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_maxFVar_3412_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_proofInstInfo_3413_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v_inferType_3414_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_getLevel_3415_);
lean_ctor_set(v_reuseFailAlloc_3440_, 5, v_congrInfo_3416_);
lean_ctor_set(v_reuseFailAlloc_3440_, 6, v_defEqI_3417_);
lean_ctor_set(v_reuseFailAlloc_3440_, 7, v_extensions_3418_);
lean_ctor_set(v_reuseFailAlloc_3440_, 8, v_issues_3419_);
lean_ctor_set(v_reuseFailAlloc_3440_, 9, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3440_, 10, v_instanceOverrides_3420_);
lean_ctor_set_uint8(v_reuseFailAlloc_3440_, sizeof(void*)*11, v_debug_3421_);
v___x_3435_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_st_ref_put(v_a_3384_, v___x_3435_);
if (v_isShared_3408_ == 0)
{
v___x_3438_ = v___x_3407_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3405_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_3442_:
{
lean_object* v_size_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_size_3445_ = lean_ctor_get(v___y_3443_, 0);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_add(v_size_3445_, v___x_3446_);
lean_inc(v_a_3405_);
v___x_3448_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3443_, v___x_3447_, v_i_3444_, v_e_3381_, v_a_3405_);
lean_dec(v_i_3444_);
v___y_3431_ = v___x_3448_;
goto v___jp_3430_;
}
v___jp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_3450_, v_e_3381_);
switch(lean_obj_tag(v___x_3451_))
{
case 0:
{
lean_object* v_index_3452_; lean_object* v_size_3453_; lean_object* v___x_3454_; 
v_index_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_index_3452_);
lean_dec_ref_known(v___x_3451_, 3);
v_size_3453_ = lean_ctor_get(v___y_3450_, 0);
lean_inc(v_size_3453_);
lean_inc(v_a_3405_);
v___x_3454_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3450_, v_size_3453_, v_index_3452_, v_e_3381_, v_a_3405_);
lean_dec(v_index_3452_);
v___y_3431_ = v___x_3454_;
goto v___jp_3430_;
}
case 1:
{
lean_object* v_index_3455_; 
v_index_3455_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_index_3455_);
lean_dec_ref_known(v___x_3451_, 1);
v___y_3443_ = v___y_3450_;
v_i_3444_ = v_index_3455_;
goto v___jp_3442_;
}
default: 
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3450_, v___x_3390_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_index_3457_; 
v_index_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_index_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___y_3443_ = v___y_3450_;
v_i_3444_ = v_index_3457_;
goto v___jp_3442_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3431_ = v___y_3450_;
goto v___jp_3430_;
}
}
}
}
v___jp_3458_:
{
lean_object* v_size_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_size_3461_ = lean_ctor_get(v___y_3459_, 0);
v___x_3462_ = lean_unsigned_to_nat(1u);
v___x_3463_ = lean_nat_add(v_size_3461_, v___x_3462_);
lean_inc(v_a_3405_);
v___x_3464_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3459_, v___x_3463_, v_i_3460_, v_e_3381_, v_a_3405_);
lean_dec(v_i_3460_);
v___y_3431_ = v___x_3464_;
goto v___jp_3430_;
}
v___jp_3465_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3425_);
lean_dec_ref(v_cache_3425_);
v___x_3467_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_3466_, v_e_3381_);
switch(lean_obj_tag(v___x_3467_))
{
case 0:
{
lean_object* v_index_3468_; lean_object* v_size_3469_; lean_object* v___x_3470_; 
v_index_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_index_3468_);
lean_dec_ref_known(v___x_3467_, 3);
v_size_3469_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_size_3469_);
lean_inc(v_a_3405_);
v___x_3470_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3466_, v_size_3469_, v_index_3468_, v_e_3381_, v_a_3405_);
lean_dec(v_index_3468_);
v___y_3431_ = v___x_3470_;
goto v___jp_3430_;
}
case 1:
{
lean_object* v_index_3471_; 
v_index_3471_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_index_3471_);
lean_dec_ref_known(v___x_3467_, 1);
v___y_3459_ = v___x_3466_;
v_i_3460_ = v_index_3471_;
goto v___jp_3458_;
}
default: 
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3466_, v___x_3390_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_index_3473_; 
v_index_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_index_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___y_3459_ = v___x_3466_;
v_i_3460_ = v_index_3473_;
goto v___jp_3458_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3431_ = v___x_3466_;
goto v___jp_3430_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_3404_;
}
}
}
else
{
lean_object* v___x_3507_; lean_object* v_canon_3508_; lean_object* v_cacheInType_3509_; lean_object* v___x_3510_; 
v___x_3507_ = lean_st_ref_get(v_a_3384_);
v_canon_3508_ = lean_ctor_get(v___x_3507_, 9);
lean_inc_ref(v_canon_3508_);
lean_dec(v___x_3507_);
v_cacheInType_3509_ = lean_ctor_get(v_canon_3508_, 1);
lean_inc_ref(v_cacheInType_3509_);
lean_dec_ref(v_canon_3508_);
v___x_3510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3509_, v_e_3381_);
lean_dec_ref(v_cacheInType_3509_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_val_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 0);
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_val_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v___x_3519_; 
lean_dec(v___x_3510_);
lean_inc_ref(v_e_3381_);
v___x_3519_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3391_, v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3621_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3621_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3621_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v_canon_3525_; lean_object* v_share_3526_; lean_object* v_maxFVar_3527_; lean_object* v_proofInstInfo_3528_; lean_object* v_inferType_3529_; lean_object* v_getLevel_3530_; lean_object* v_congrInfo_3531_; lean_object* v_defEqI_3532_; lean_object* v_extensions_3533_; lean_object* v_issues_3534_; lean_object* v_instanceOverrides_3535_; uint8_t v_debug_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3620_; 
v___x_3524_ = lean_st_ref_take(v_a_3384_);
v_canon_3525_ = lean_ctor_get(v___x_3524_, 9);
v_share_3526_ = lean_ctor_get(v___x_3524_, 0);
v_maxFVar_3527_ = lean_ctor_get(v___x_3524_, 1);
v_proofInstInfo_3528_ = lean_ctor_get(v___x_3524_, 2);
v_inferType_3529_ = lean_ctor_get(v___x_3524_, 3);
v_getLevel_3530_ = lean_ctor_get(v___x_3524_, 4);
v_congrInfo_3531_ = lean_ctor_get(v___x_3524_, 5);
v_defEqI_3532_ = lean_ctor_get(v___x_3524_, 6);
v_extensions_3533_ = lean_ctor_get(v___x_3524_, 7);
v_issues_3534_ = lean_ctor_get(v___x_3524_, 8);
v_instanceOverrides_3535_ = lean_ctor_get(v___x_3524_, 10);
v_debug_3536_ = lean_ctor_get_uint8(v___x_3524_, sizeof(void*)*11);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3538_ = v___x_3524_;
v_isShared_3539_ = v_isSharedCheck_3620_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_instanceOverrides_3535_);
lean_inc(v_canon_3525_);
lean_inc(v_issues_3534_);
lean_inc(v_extensions_3533_);
lean_inc(v_defEqI_3532_);
lean_inc(v_congrInfo_3531_);
lean_inc(v_getLevel_3530_);
lean_inc(v_inferType_3529_);
lean_inc(v_proofInstInfo_3528_);
lean_inc(v_maxFVar_3527_);
lean_inc(v_share_3526_);
lean_dec(v___x_3524_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3620_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_cache_3540_; lean_object* v_cacheInType_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3619_; 
v_cache_3540_ = lean_ctor_get(v_canon_3525_, 0);
v_cacheInType_3541_ = lean_ctor_get(v_canon_3525_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_canon_3525_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3543_ = v_canon_3525_;
v_isShared_3544_ = v_isSharedCheck_3619_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_cacheInType_3541_);
lean_inc(v_cache_3540_);
lean_dec(v_canon_3525_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3619_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___y_3546_; lean_object* v___y_3558_; lean_object* v_i_3559_; lean_object* v___y_3574_; lean_object* v_i_3575_; lean_object* v___y_3581_; lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3541_, v_e_3381_);
switch(lean_obj_tag(v___x_3589_))
{
case 0:
{
lean_object* v_index_3590_; lean_object* v_size_3591_; lean_object* v___x_3592_; 
v_index_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_index_3590_);
lean_dec_ref_known(v___x_3589_, 3);
v_size_3591_ = lean_ctor_get(v_cacheInType_3541_, 0);
lean_inc(v_size_3591_);
lean_inc(v_a_3520_);
v___x_3592_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_3541_, v_size_3591_, v_index_3590_, v_e_3381_, v_a_3520_);
lean_dec(v_index_3590_);
v___y_3546_ = v___x_3592_;
goto v___jp_3545_;
}
case 1:
{
lean_object* v_index_3593_; lean_object* v_size_3594_; lean_object* v_keyArray_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_index_3593_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_index_3593_);
lean_dec_ref_known(v___x_3589_, 1);
v_size_3594_ = lean_ctor_get(v_cacheInType_3541_, 0);
v_keyArray_3595_ = lean_ctor_get(v_cacheInType_3541_, 1);
v___x_3596_ = lean_unsigned_to_nat(1u);
v___x_3597_ = lean_nat_add(v_size_3594_, v___x_3596_);
v___x_3598_ = lean_array_get_size(v_keyArray_3595_);
v___x_3599_ = lean_nat_dec_lt(v___x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_dec(v___x_3597_);
lean_dec(v_index_3593_);
goto v___jp_3564_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3600_ = lean_unsigned_to_nat(4u);
v___x_3601_ = lean_nat_mul(v___x_3597_, v___x_3600_);
v___x_3602_ = lean_unsigned_to_nat(3u);
v___x_3603_ = lean_nat_mul(v___x_3598_, v___x_3602_);
v___x_3604_ = lean_nat_dec_le(v___x_3601_, v___x_3603_);
lean_dec(v___x_3603_);
lean_dec(v___x_3601_);
if (v___x_3604_ == 0)
{
lean_dec(v___x_3597_);
lean_dec(v_index_3593_);
goto v___jp_3564_;
}
else
{
lean_object* v___x_3605_; 
lean_inc(v_a_3520_);
v___x_3605_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_3541_, v___x_3597_, v_index_3593_, v_e_3381_, v_a_3520_);
lean_dec(v_index_3593_);
v___y_3546_ = v___x_3605_;
goto v___jp_3545_;
}
}
}
default: 
{
lean_object* v_size_3606_; lean_object* v_keyArray_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_size_3606_ = lean_ctor_get(v_cacheInType_3541_, 0);
v_keyArray_3607_ = lean_ctor_get(v_cacheInType_3541_, 1);
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_size_3606_, v___x_3608_);
v___x_3610_ = lean_array_get_size(v_keyArray_3607_);
v___x_3611_ = lean_nat_dec_lt(v___x_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v___x_3609_);
v___x_3612_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3541_);
lean_dec_ref(v_cacheInType_3541_);
v___y_3581_ = v___x_3612_;
goto v___jp_3580_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
v___x_3613_ = lean_unsigned_to_nat(4u);
v___x_3614_ = lean_nat_mul(v___x_3609_, v___x_3613_);
lean_dec(v___x_3609_);
v___x_3615_ = lean_unsigned_to_nat(3u);
v___x_3616_ = lean_nat_mul(v___x_3610_, v___x_3615_);
v___x_3617_ = lean_nat_dec_le(v___x_3614_, v___x_3616_);
lean_dec(v___x_3616_);
lean_dec(v___x_3614_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3541_);
lean_dec_ref(v_cacheInType_3541_);
v___y_3581_ = v___x_3618_;
goto v___jp_3580_;
}
else
{
v___y_3581_ = v_cacheInType_3541_;
goto v___jp_3580_;
}
}
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v___y_3546_);
v___x_3548_ = v___x_3543_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_cache_3540_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___y_3546_);
v___x_3548_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 9, v___x_3548_);
v___x_3550_ = v___x_3538_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_share_3526_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_maxFVar_3527_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_proofInstInfo_3528_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_inferType_3529_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_getLevel_3530_);
lean_ctor_set(v_reuseFailAlloc_3555_, 5, v_congrInfo_3531_);
lean_ctor_set(v_reuseFailAlloc_3555_, 6, v_defEqI_3532_);
lean_ctor_set(v_reuseFailAlloc_3555_, 7, v_extensions_3533_);
lean_ctor_set(v_reuseFailAlloc_3555_, 8, v_issues_3534_);
lean_ctor_set(v_reuseFailAlloc_3555_, 9, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3555_, 10, v_instanceOverrides_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3555_, sizeof(void*)*11, v_debug_3536_);
v___x_3550_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = lean_st_ref_put(v_a_3384_, v___x_3550_);
if (v_isShared_3523_ == 0)
{
v___x_3553_ = v___x_3522_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3520_);
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
v___jp_3557_:
{
lean_object* v_size_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_size_3560_ = lean_ctor_get(v___y_3558_, 0);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_nat_add(v_size_3560_, v___x_3561_);
lean_inc(v_a_3520_);
v___x_3563_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3558_, v___x_3562_, v_i_3559_, v_e_3381_, v_a_3520_);
lean_dec(v_i_3559_);
v___y_3546_ = v___x_3563_;
goto v___jp_3545_;
}
v___jp_3564_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3541_);
lean_dec_ref(v_cacheInType_3541_);
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_3565_, v_e_3381_);
switch(lean_obj_tag(v___x_3566_))
{
case 0:
{
lean_object* v_index_3567_; lean_object* v_size_3568_; lean_object* v___x_3569_; 
v_index_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_index_3567_);
lean_dec_ref_known(v___x_3566_, 3);
v_size_3568_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_size_3568_);
lean_inc(v_a_3520_);
v___x_3569_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3565_, v_size_3568_, v_index_3567_, v_e_3381_, v_a_3520_);
lean_dec(v_index_3567_);
v___y_3546_ = v___x_3569_;
goto v___jp_3545_;
}
case 1:
{
lean_object* v_index_3570_; 
v_index_3570_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_index_3570_);
lean_dec_ref_known(v___x_3566_, 1);
v___y_3558_ = v___x_3565_;
v_i_3559_ = v_index_3570_;
goto v___jp_3557_;
}
default: 
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3565_, v___x_3390_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_index_3572_; 
v_index_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_index_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v___y_3558_ = v___x_3565_;
v_i_3559_ = v_index_3572_;
goto v___jp_3557_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3546_ = v___x_3565_;
goto v___jp_3545_;
}
}
}
}
v___jp_3573_:
{
lean_object* v_size_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_size_3576_ = lean_ctor_get(v___y_3574_, 0);
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_nat_add(v_size_3576_, v___x_3577_);
lean_inc(v_a_3520_);
v___x_3579_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3574_, v___x_3578_, v_i_3575_, v_e_3381_, v_a_3520_);
lean_dec(v_i_3575_);
v___y_3546_ = v___x_3579_;
goto v___jp_3545_;
}
v___jp_3580_:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_3581_, v_e_3381_);
switch(lean_obj_tag(v___x_3582_))
{
case 0:
{
lean_object* v_index_3583_; lean_object* v_size_3584_; lean_object* v___x_3585_; 
v_index_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_index_3583_);
lean_dec_ref_known(v___x_3582_, 3);
v_size_3584_ = lean_ctor_get(v___y_3581_, 0);
lean_inc(v_size_3584_);
lean_inc(v_a_3520_);
v___x_3585_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3581_, v_size_3584_, v_index_3583_, v_e_3381_, v_a_3520_);
lean_dec(v_index_3583_);
v___y_3546_ = v___x_3585_;
goto v___jp_3545_;
}
case 1:
{
lean_object* v_index_3586_; 
v_index_3586_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_index_3586_);
lean_dec_ref_known(v___x_3582_, 1);
v___y_3574_ = v___y_3581_;
v_i_3575_ = v_index_3586_;
goto v___jp_3573_;
}
default: 
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3581_, v___x_3390_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_index_3588_; 
v_index_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_index_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___y_3574_ = v___y_3581_;
v_i_3575_ = v_index_3588_;
goto v___jp_3573_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3546_ = v___y_3581_;
goto v___jp_3545_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_3519_;
}
}
}
}
case 6:
{
if (v_a_3382_ == 0)
{
lean_object* v___x_3622_; lean_object* v_canon_3623_; lean_object* v_cache_3624_; lean_object* v___x_3625_; 
v___x_3622_ = lean_st_ref_get(v_a_3384_);
v_canon_3623_ = lean_ctor_get(v___x_3622_, 9);
lean_inc_ref(v_canon_3623_);
lean_dec(v___x_3622_);
v_cache_3624_ = lean_ctor_get(v_canon_3623_, 0);
lean_inc_ref(v_cache_3624_);
lean_dec_ref(v_canon_3623_);
v___x_3625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3624_, v_e_3381_);
lean_dec_ref(v_cache_3624_);
if (lean_obj_tag(v___x_3625_) == 1)
{
lean_object* v_val_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_val_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 0);
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_val_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
else
{
lean_object* v___x_3634_; 
lean_dec(v___x_3625_);
lean_inc_ref(v_e_3381_);
v___x_3634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3738_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3738_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3738_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v_canon_3640_; lean_object* v_share_3641_; lean_object* v_maxFVar_3642_; lean_object* v_proofInstInfo_3643_; lean_object* v_inferType_3644_; lean_object* v_getLevel_3645_; lean_object* v_congrInfo_3646_; lean_object* v_defEqI_3647_; lean_object* v_extensions_3648_; lean_object* v_issues_3649_; lean_object* v_instanceOverrides_3650_; uint8_t v_debug_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3737_; 
v___x_3639_ = lean_st_ref_take(v_a_3384_);
v_canon_3640_ = lean_ctor_get(v___x_3639_, 9);
v_share_3641_ = lean_ctor_get(v___x_3639_, 0);
v_maxFVar_3642_ = lean_ctor_get(v___x_3639_, 1);
v_proofInstInfo_3643_ = lean_ctor_get(v___x_3639_, 2);
v_inferType_3644_ = lean_ctor_get(v___x_3639_, 3);
v_getLevel_3645_ = lean_ctor_get(v___x_3639_, 4);
v_congrInfo_3646_ = lean_ctor_get(v___x_3639_, 5);
v_defEqI_3647_ = lean_ctor_get(v___x_3639_, 6);
v_extensions_3648_ = lean_ctor_get(v___x_3639_, 7);
v_issues_3649_ = lean_ctor_get(v___x_3639_, 8);
v_instanceOverrides_3650_ = lean_ctor_get(v___x_3639_, 10);
v_debug_3651_ = lean_ctor_get_uint8(v___x_3639_, sizeof(void*)*11);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3653_ = v___x_3639_;
v_isShared_3654_ = v_isSharedCheck_3737_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_instanceOverrides_3650_);
lean_inc(v_canon_3640_);
lean_inc(v_issues_3649_);
lean_inc(v_extensions_3648_);
lean_inc(v_defEqI_3647_);
lean_inc(v_congrInfo_3646_);
lean_inc(v_getLevel_3645_);
lean_inc(v_inferType_3644_);
lean_inc(v_proofInstInfo_3643_);
lean_inc(v_maxFVar_3642_);
lean_inc(v_share_3641_);
lean_dec(v___x_3639_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3737_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_cache_3655_; lean_object* v_cacheInType_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3736_; 
v_cache_3655_ = lean_ctor_get(v_canon_3640_, 0);
v_cacheInType_3656_ = lean_ctor_get(v_canon_3640_, 1);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_canon_3640_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3658_ = v_canon_3640_;
v_isShared_3659_ = v_isSharedCheck_3736_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_cacheInType_3656_);
lean_inc(v_cache_3655_);
lean_dec(v_canon_3640_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3736_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___y_3661_; lean_object* v___y_3673_; lean_object* v_i_3674_; lean_object* v___y_3680_; lean_object* v___y_3690_; lean_object* v_i_3691_; lean_object* v___x_3706_; 
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3655_, v_e_3381_);
switch(lean_obj_tag(v___x_3706_))
{
case 0:
{
lean_object* v_index_3707_; lean_object* v_size_3708_; lean_object* v___x_3709_; 
v_index_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_index_3707_);
lean_dec_ref_known(v___x_3706_, 3);
v_size_3708_ = lean_ctor_get(v_cache_3655_, 0);
lean_inc(v_size_3708_);
lean_inc(v_a_3635_);
v___x_3709_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3655_, v_size_3708_, v_index_3707_, v_e_3381_, v_a_3635_);
lean_dec(v_index_3707_);
v___y_3661_ = v___x_3709_;
goto v___jp_3660_;
}
case 1:
{
lean_object* v_index_3710_; lean_object* v_size_3711_; lean_object* v_keyArray_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_index_3710_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_index_3710_);
lean_dec_ref_known(v___x_3706_, 1);
v_size_3711_ = lean_ctor_get(v_cache_3655_, 0);
v_keyArray_3712_ = lean_ctor_get(v_cache_3655_, 1);
v___x_3713_ = lean_unsigned_to_nat(1u);
v___x_3714_ = lean_nat_add(v_size_3711_, v___x_3713_);
v___x_3715_ = lean_array_get_size(v_keyArray_3712_);
v___x_3716_ = lean_nat_dec_lt(v___x_3714_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_dec(v___x_3714_);
lean_dec(v_index_3710_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3717_ = lean_unsigned_to_nat(4u);
v___x_3718_ = lean_nat_mul(v___x_3714_, v___x_3717_);
v___x_3719_ = lean_unsigned_to_nat(3u);
v___x_3720_ = lean_nat_mul(v___x_3715_, v___x_3719_);
v___x_3721_ = lean_nat_dec_le(v___x_3718_, v___x_3720_);
lean_dec(v___x_3720_);
lean_dec(v___x_3718_);
if (v___x_3721_ == 0)
{
lean_dec(v___x_3714_);
lean_dec(v_index_3710_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3722_; 
lean_inc(v_a_3635_);
v___x_3722_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3655_, v___x_3714_, v_index_3710_, v_e_3381_, v_a_3635_);
lean_dec(v_index_3710_);
v___y_3661_ = v___x_3722_;
goto v___jp_3660_;
}
}
}
default: 
{
lean_object* v_size_3723_; lean_object* v_keyArray_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v_size_3723_ = lean_ctor_get(v_cache_3655_, 0);
v_keyArray_3724_ = lean_ctor_get(v_cache_3655_, 1);
v___x_3725_ = lean_unsigned_to_nat(1u);
v___x_3726_ = lean_nat_add(v_size_3723_, v___x_3725_);
v___x_3727_ = lean_array_get_size(v_keyArray_3724_);
v___x_3728_ = lean_nat_dec_lt(v___x_3726_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v___x_3726_);
v___x_3729_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3655_);
lean_dec_ref(v_cache_3655_);
v___y_3680_ = v___x_3729_;
goto v___jp_3679_;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3730_ = lean_unsigned_to_nat(4u);
v___x_3731_ = lean_nat_mul(v___x_3726_, v___x_3730_);
lean_dec(v___x_3726_);
v___x_3732_ = lean_unsigned_to_nat(3u);
v___x_3733_ = lean_nat_mul(v___x_3727_, v___x_3732_);
v___x_3734_ = lean_nat_dec_le(v___x_3731_, v___x_3733_);
lean_dec(v___x_3733_);
lean_dec(v___x_3731_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3655_);
lean_dec_ref(v_cache_3655_);
v___y_3680_ = v___x_3735_;
goto v___jp_3679_;
}
else
{
v___y_3680_ = v_cache_3655_;
goto v___jp_3679_;
}
}
}
}
v___jp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___y_3661_);
v___x_3663_ = v___x_3658_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___y_3661_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_cacheInType_3656_);
v___x_3663_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 9, v___x_3663_);
v___x_3665_ = v___x_3653_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_share_3641_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_maxFVar_3642_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_proofInstInfo_3643_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_inferType_3644_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_getLevel_3645_);
lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_congrInfo_3646_);
lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_defEqI_3647_);
lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_extensions_3648_);
lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_issues_3649_);
lean_ctor_set(v_reuseFailAlloc_3670_, 9, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3670_, 10, v_instanceOverrides_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3670_, sizeof(void*)*11, v_debug_3651_);
v___x_3665_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3666_ = lean_st_ref_put(v_a_3384_, v___x_3665_);
if (v_isShared_3638_ == 0)
{
v___x_3668_ = v___x_3637_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3635_);
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
v___jp_3672_:
{
lean_object* v_size_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_size_3675_ = lean_ctor_get(v___y_3673_, 0);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = lean_nat_add(v_size_3675_, v___x_3676_);
lean_inc(v_a_3635_);
v___x_3678_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3673_, v___x_3677_, v_i_3674_, v_e_3381_, v_a_3635_);
lean_dec(v_i_3674_);
v___y_3661_ = v___x_3678_;
goto v___jp_3660_;
}
v___jp_3679_:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_3680_, v_e_3381_);
switch(lean_obj_tag(v___x_3681_))
{
case 0:
{
lean_object* v_index_3682_; lean_object* v_size_3683_; lean_object* v___x_3684_; 
v_index_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_index_3682_);
lean_dec_ref_known(v___x_3681_, 3);
v_size_3683_ = lean_ctor_get(v___y_3680_, 0);
lean_inc(v_size_3683_);
lean_inc(v_a_3635_);
v___x_3684_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3680_, v_size_3683_, v_index_3682_, v_e_3381_, v_a_3635_);
lean_dec(v_index_3682_);
v___y_3661_ = v___x_3684_;
goto v___jp_3660_;
}
case 1:
{
lean_object* v_index_3685_; 
v_index_3685_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_index_3685_);
lean_dec_ref_known(v___x_3681_, 1);
v___y_3673_ = v___y_3680_;
v_i_3674_ = v_index_3685_;
goto v___jp_3672_;
}
default: 
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3680_, v___x_3686_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_index_3688_; 
v_index_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_index_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___y_3673_ = v___y_3680_;
v_i_3674_ = v_index_3688_;
goto v___jp_3672_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3661_ = v___y_3680_;
goto v___jp_3660_;
}
}
}
}
v___jp_3689_:
{
lean_object* v_size_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_size_3692_ = lean_ctor_get(v___y_3690_, 0);
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_size_3692_, v___x_3693_);
lean_inc(v_a_3635_);
v___x_3695_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3690_, v___x_3694_, v_i_3691_, v_e_3381_, v_a_3635_);
lean_dec(v_i_3691_);
v___y_3661_ = v___x_3695_;
goto v___jp_3660_;
}
v___jp_3696_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3655_);
lean_dec_ref(v_cache_3655_);
v___x_3698_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_3697_, v_e_3381_);
switch(lean_obj_tag(v___x_3698_))
{
case 0:
{
lean_object* v_index_3699_; lean_object* v_size_3700_; lean_object* v___x_3701_; 
v_index_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_index_3699_);
lean_dec_ref_known(v___x_3698_, 3);
v_size_3700_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_size_3700_);
lean_inc(v_a_3635_);
v___x_3701_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3697_, v_size_3700_, v_index_3699_, v_e_3381_, v_a_3635_);
lean_dec(v_index_3699_);
v___y_3661_ = v___x_3701_;
goto v___jp_3660_;
}
case 1:
{
lean_object* v_index_3702_; 
v_index_3702_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_index_3702_);
lean_dec_ref_known(v___x_3698_, 1);
v___y_3690_ = v___x_3697_;
v_i_3691_ = v_index_3702_;
goto v___jp_3689_;
}
default: 
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3697_, v___x_3703_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_index_3705_; 
v_index_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_index_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___y_3690_ = v___x_3697_;
v_i_3691_ = v_index_3705_;
goto v___jp_3689_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3661_ = v___x_3697_;
goto v___jp_3660_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_3634_;
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v_canon_3740_; lean_object* v_cacheInType_3741_; lean_object* v___x_3742_; 
v___x_3739_ = lean_st_ref_get(v_a_3384_);
v_canon_3740_ = lean_ctor_get(v___x_3739_, 9);
lean_inc_ref(v_canon_3740_);
lean_dec(v___x_3739_);
v_cacheInType_3741_ = lean_ctor_get(v_canon_3740_, 1);
lean_inc_ref(v_cacheInType_3741_);
lean_dec_ref(v_canon_3740_);
v___x_3742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3741_, v_e_3381_);
lean_dec_ref(v_cacheInType_3741_);
if (lean_obj_tag(v___x_3742_) == 1)
{
lean_object* v_val_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_val_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set_tag(v___x_3745_, 0);
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_val_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
else
{
lean_object* v___x_3751_; 
lean_dec(v___x_3742_);
lean_inc_ref(v_e_3381_);
v___x_3751_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3855_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3855_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3855_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v_canon_3757_; lean_object* v_share_3758_; lean_object* v_maxFVar_3759_; lean_object* v_proofInstInfo_3760_; lean_object* v_inferType_3761_; lean_object* v_getLevel_3762_; lean_object* v_congrInfo_3763_; lean_object* v_defEqI_3764_; lean_object* v_extensions_3765_; lean_object* v_issues_3766_; lean_object* v_instanceOverrides_3767_; uint8_t v_debug_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3854_; 
v___x_3756_ = lean_st_ref_take(v_a_3384_);
v_canon_3757_ = lean_ctor_get(v___x_3756_, 9);
v_share_3758_ = lean_ctor_get(v___x_3756_, 0);
v_maxFVar_3759_ = lean_ctor_get(v___x_3756_, 1);
v_proofInstInfo_3760_ = lean_ctor_get(v___x_3756_, 2);
v_inferType_3761_ = lean_ctor_get(v___x_3756_, 3);
v_getLevel_3762_ = lean_ctor_get(v___x_3756_, 4);
v_congrInfo_3763_ = lean_ctor_get(v___x_3756_, 5);
v_defEqI_3764_ = lean_ctor_get(v___x_3756_, 6);
v_extensions_3765_ = lean_ctor_get(v___x_3756_, 7);
v_issues_3766_ = lean_ctor_get(v___x_3756_, 8);
v_instanceOverrides_3767_ = lean_ctor_get(v___x_3756_, 10);
v_debug_3768_ = lean_ctor_get_uint8(v___x_3756_, sizeof(void*)*11);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3770_ = v___x_3756_;
v_isShared_3771_ = v_isSharedCheck_3854_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_instanceOverrides_3767_);
lean_inc(v_canon_3757_);
lean_inc(v_issues_3766_);
lean_inc(v_extensions_3765_);
lean_inc(v_defEqI_3764_);
lean_inc(v_congrInfo_3763_);
lean_inc(v_getLevel_3762_);
lean_inc(v_inferType_3761_);
lean_inc(v_proofInstInfo_3760_);
lean_inc(v_maxFVar_3759_);
lean_inc(v_share_3758_);
lean_dec(v___x_3756_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3854_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_cache_3772_; lean_object* v_cacheInType_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3853_; 
v_cache_3772_ = lean_ctor_get(v_canon_3757_, 0);
v_cacheInType_3773_ = lean_ctor_get(v_canon_3757_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_canon_3757_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3775_ = v_canon_3757_;
v_isShared_3776_ = v_isSharedCheck_3853_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_cacheInType_3773_);
lean_inc(v_cache_3772_);
lean_dec(v_canon_3757_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3853_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___y_3778_; lean_object* v___y_3790_; lean_object* v_i_3791_; lean_object* v___y_3807_; lean_object* v_i_3808_; lean_object* v___y_3814_; lean_object* v___x_3823_; 
v___x_3823_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3773_, v_e_3381_);
switch(lean_obj_tag(v___x_3823_))
{
case 0:
{
lean_object* v_index_3824_; lean_object* v_size_3825_; lean_object* v___x_3826_; 
v_index_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_index_3824_);
lean_dec_ref_known(v___x_3823_, 3);
v_size_3825_ = lean_ctor_get(v_cacheInType_3773_, 0);
lean_inc(v_size_3825_);
lean_inc(v_a_3752_);
v___x_3826_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_3773_, v_size_3825_, v_index_3824_, v_e_3381_, v_a_3752_);
lean_dec(v_index_3824_);
v___y_3778_ = v___x_3826_;
goto v___jp_3777_;
}
case 1:
{
lean_object* v_index_3827_; lean_object* v_size_3828_; lean_object* v_keyArray_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_index_3827_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_index_3827_);
lean_dec_ref_known(v___x_3823_, 1);
v_size_3828_ = lean_ctor_get(v_cacheInType_3773_, 0);
v_keyArray_3829_ = lean_ctor_get(v_cacheInType_3773_, 1);
v___x_3830_ = lean_unsigned_to_nat(1u);
v___x_3831_ = lean_nat_add(v_size_3828_, v___x_3830_);
v___x_3832_ = lean_array_get_size(v_keyArray_3829_);
v___x_3833_ = lean_nat_dec_lt(v___x_3831_, v___x_3832_);
if (v___x_3833_ == 0)
{
lean_dec(v___x_3831_);
lean_dec(v_index_3827_);
goto v___jp_3796_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3834_ = lean_unsigned_to_nat(4u);
v___x_3835_ = lean_nat_mul(v___x_3831_, v___x_3834_);
v___x_3836_ = lean_unsigned_to_nat(3u);
v___x_3837_ = lean_nat_mul(v___x_3832_, v___x_3836_);
v___x_3838_ = lean_nat_dec_le(v___x_3835_, v___x_3837_);
lean_dec(v___x_3837_);
lean_dec(v___x_3835_);
if (v___x_3838_ == 0)
{
lean_dec(v___x_3831_);
lean_dec(v_index_3827_);
goto v___jp_3796_;
}
else
{
lean_object* v___x_3839_; 
lean_inc(v_a_3752_);
v___x_3839_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_3773_, v___x_3831_, v_index_3827_, v_e_3381_, v_a_3752_);
lean_dec(v_index_3827_);
v___y_3778_ = v___x_3839_;
goto v___jp_3777_;
}
}
}
default: 
{
lean_object* v_size_3840_; lean_object* v_keyArray_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v_size_3840_ = lean_ctor_get(v_cacheInType_3773_, 0);
v_keyArray_3841_ = lean_ctor_get(v_cacheInType_3773_, 1);
v___x_3842_ = lean_unsigned_to_nat(1u);
v___x_3843_ = lean_nat_add(v_size_3840_, v___x_3842_);
v___x_3844_ = lean_array_get_size(v_keyArray_3841_);
v___x_3845_ = lean_nat_dec_lt(v___x_3843_, v___x_3844_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; 
lean_dec(v___x_3843_);
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3773_);
lean_dec_ref(v_cacheInType_3773_);
v___y_3814_ = v___x_3846_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3847_ = lean_unsigned_to_nat(4u);
v___x_3848_ = lean_nat_mul(v___x_3843_, v___x_3847_);
lean_dec(v___x_3843_);
v___x_3849_ = lean_unsigned_to_nat(3u);
v___x_3850_ = lean_nat_mul(v___x_3844_, v___x_3849_);
v___x_3851_ = lean_nat_dec_le(v___x_3848_, v___x_3850_);
lean_dec(v___x_3850_);
lean_dec(v___x_3848_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3773_);
lean_dec_ref(v_cacheInType_3773_);
v___y_3814_ = v___x_3852_;
goto v___jp_3813_;
}
else
{
v___y_3814_ = v_cacheInType_3773_;
goto v___jp_3813_;
}
}
}
}
v___jp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___y_3778_);
v___x_3780_ = v___x_3775_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_cache_3772_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___y_3778_);
v___x_3780_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3782_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 9, v___x_3780_);
v___x_3782_ = v___x_3770_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_share_3758_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_maxFVar_3759_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_proofInstInfo_3760_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v_inferType_3761_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v_getLevel_3762_);
lean_ctor_set(v_reuseFailAlloc_3787_, 5, v_congrInfo_3763_);
lean_ctor_set(v_reuseFailAlloc_3787_, 6, v_defEqI_3764_);
lean_ctor_set(v_reuseFailAlloc_3787_, 7, v_extensions_3765_);
lean_ctor_set(v_reuseFailAlloc_3787_, 8, v_issues_3766_);
lean_ctor_set(v_reuseFailAlloc_3787_, 9, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3787_, 10, v_instanceOverrides_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3787_, sizeof(void*)*11, v_debug_3768_);
v___x_3782_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_st_ref_put(v_a_3384_, v___x_3782_);
if (v_isShared_3755_ == 0)
{
v___x_3785_ = v___x_3754_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3752_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
v___jp_3789_:
{
lean_object* v_size_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v_size_3792_ = lean_ctor_get(v___y_3790_, 0);
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_nat_add(v_size_3792_, v___x_3793_);
lean_inc(v_a_3752_);
v___x_3795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3790_, v___x_3794_, v_i_3791_, v_e_3381_, v_a_3752_);
lean_dec(v_i_3791_);
v___y_3778_ = v___x_3795_;
goto v___jp_3777_;
}
v___jp_3796_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_3773_);
lean_dec_ref(v_cacheInType_3773_);
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_3797_, v_e_3381_);
switch(lean_obj_tag(v___x_3798_))
{
case 0:
{
lean_object* v_index_3799_; lean_object* v_size_3800_; lean_object* v___x_3801_; 
v_index_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_index_3799_);
lean_dec_ref_known(v___x_3798_, 3);
v_size_3800_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_size_3800_);
lean_inc(v_a_3752_);
v___x_3801_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3797_, v_size_3800_, v_index_3799_, v_e_3381_, v_a_3752_);
lean_dec(v_index_3799_);
v___y_3778_ = v___x_3801_;
goto v___jp_3777_;
}
case 1:
{
lean_object* v_index_3802_; 
v_index_3802_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_index_3802_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3790_ = v___x_3797_;
v_i_3791_ = v_index_3802_;
goto v___jp_3789_;
}
default: 
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3797_, v___x_3803_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_index_3805_; 
v_index_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_index_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3790_ = v___x_3797_;
v_i_3791_ = v_index_3805_;
goto v___jp_3789_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3778_ = v___x_3797_;
goto v___jp_3777_;
}
}
}
}
v___jp_3806_:
{
lean_object* v_size_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_size_3809_ = lean_ctor_get(v___y_3807_, 0);
v___x_3810_ = lean_unsigned_to_nat(1u);
v___x_3811_ = lean_nat_add(v_size_3809_, v___x_3810_);
lean_inc(v_a_3752_);
v___x_3812_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3807_, v___x_3811_, v_i_3808_, v_e_3381_, v_a_3752_);
lean_dec(v_i_3808_);
v___y_3778_ = v___x_3812_;
goto v___jp_3777_;
}
v___jp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_3814_, v_e_3381_);
switch(lean_obj_tag(v___x_3815_))
{
case 0:
{
lean_object* v_index_3816_; lean_object* v_size_3817_; lean_object* v___x_3818_; 
v_index_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_index_3816_);
lean_dec_ref_known(v___x_3815_, 3);
v_size_3817_ = lean_ctor_get(v___y_3814_, 0);
lean_inc(v_size_3817_);
lean_inc(v_a_3752_);
v___x_3818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3814_, v_size_3817_, v_index_3816_, v_e_3381_, v_a_3752_);
lean_dec(v_index_3816_);
v___y_3778_ = v___x_3818_;
goto v___jp_3777_;
}
case 1:
{
lean_object* v_index_3819_; 
v_index_3819_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_index_3819_);
lean_dec_ref_known(v___x_3815_, 1);
v___y_3807_ = v___y_3814_;
v_i_3808_ = v_index_3819_;
goto v___jp_3806_;
}
default: 
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3814_, v___x_3820_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_index_3822_; 
v_index_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_index_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___y_3807_ = v___y_3814_;
v_i_3808_ = v_index_3822_;
goto v___jp_3806_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_3778_ = v___y_3814_;
goto v___jp_3777_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_3751_;
}
}
}
}
case 8:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_unsigned_to_nat(0u);
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3382_ == 0)
{
lean_object* v___x_3858_; lean_object* v_canon_3859_; lean_object* v_cache_3860_; lean_object* v___x_3861_; 
v___x_3858_ = lean_st_ref_get(v_a_3384_);
v_canon_3859_ = lean_ctor_get(v___x_3858_, 9);
lean_inc_ref(v_canon_3859_);
lean_dec(v___x_3858_);
v_cache_3860_ = lean_ctor_get(v_canon_3859_, 0);
lean_inc_ref(v_cache_3860_);
lean_dec_ref(v_canon_3859_);
v___x_3861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3860_, v_e_3381_);
lean_dec_ref(v_cache_3860_);
if (lean_obj_tag(v___x_3861_) == 1)
{
lean_object* v_val_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref_known(v_e_3381_, 4);
v_val_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_val_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set_tag(v___x_3864_, 0);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_val_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
else
{
lean_object* v___x_3870_; 
lean_dec(v___x_3861_);
lean_inc_ref(v_e_3381_);
v___x_3870_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3857_, v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3972_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3972_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3972_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v_canon_3876_; lean_object* v_share_3877_; lean_object* v_maxFVar_3878_; lean_object* v_proofInstInfo_3879_; lean_object* v_inferType_3880_; lean_object* v_getLevel_3881_; lean_object* v_congrInfo_3882_; lean_object* v_defEqI_3883_; lean_object* v_extensions_3884_; lean_object* v_issues_3885_; lean_object* v_instanceOverrides_3886_; uint8_t v_debug_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3971_; 
v___x_3875_ = lean_st_ref_take(v_a_3384_);
v_canon_3876_ = lean_ctor_get(v___x_3875_, 9);
v_share_3877_ = lean_ctor_get(v___x_3875_, 0);
v_maxFVar_3878_ = lean_ctor_get(v___x_3875_, 1);
v_proofInstInfo_3879_ = lean_ctor_get(v___x_3875_, 2);
v_inferType_3880_ = lean_ctor_get(v___x_3875_, 3);
v_getLevel_3881_ = lean_ctor_get(v___x_3875_, 4);
v_congrInfo_3882_ = lean_ctor_get(v___x_3875_, 5);
v_defEqI_3883_ = lean_ctor_get(v___x_3875_, 6);
v_extensions_3884_ = lean_ctor_get(v___x_3875_, 7);
v_issues_3885_ = lean_ctor_get(v___x_3875_, 8);
v_instanceOverrides_3886_ = lean_ctor_get(v___x_3875_, 10);
v_debug_3887_ = lean_ctor_get_uint8(v___x_3875_, sizeof(void*)*11);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3889_ = v___x_3875_;
v_isShared_3890_ = v_isSharedCheck_3971_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_instanceOverrides_3886_);
lean_inc(v_canon_3876_);
lean_inc(v_issues_3885_);
lean_inc(v_extensions_3884_);
lean_inc(v_defEqI_3883_);
lean_inc(v_congrInfo_3882_);
lean_inc(v_getLevel_3881_);
lean_inc(v_inferType_3880_);
lean_inc(v_proofInstInfo_3879_);
lean_inc(v_maxFVar_3878_);
lean_inc(v_share_3877_);
lean_dec(v___x_3875_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3971_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v_cache_3891_; lean_object* v_cacheInType_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3970_; 
v_cache_3891_ = lean_ctor_get(v_canon_3876_, 0);
v_cacheInType_3892_ = lean_ctor_get(v_canon_3876_, 1);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_canon_3876_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3894_ = v_canon_3876_;
v_isShared_3895_ = v_isSharedCheck_3970_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_cacheInType_3892_);
lean_inc(v_cache_3891_);
lean_dec(v_canon_3876_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3970_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___y_3897_; lean_object* v___y_3909_; lean_object* v_i_3910_; lean_object* v___y_3916_; lean_object* v___y_3925_; lean_object* v_i_3926_; lean_object* v___x_3940_; 
v___x_3940_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3891_, v_e_3381_);
switch(lean_obj_tag(v___x_3940_))
{
case 0:
{
lean_object* v_index_3941_; lean_object* v_size_3942_; lean_object* v___x_3943_; 
v_index_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_index_3941_);
lean_dec_ref_known(v___x_3940_, 3);
v_size_3942_ = lean_ctor_get(v_cache_3891_, 0);
lean_inc(v_size_3942_);
lean_inc(v_a_3871_);
v___x_3943_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3891_, v_size_3942_, v_index_3941_, v_e_3381_, v_a_3871_);
lean_dec(v_index_3941_);
v___y_3897_ = v___x_3943_;
goto v___jp_3896_;
}
case 1:
{
lean_object* v_index_3944_; lean_object* v_size_3945_; lean_object* v_keyArray_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v_index_3944_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_index_3944_);
lean_dec_ref_known(v___x_3940_, 1);
v_size_3945_ = lean_ctor_get(v_cache_3891_, 0);
v_keyArray_3946_ = lean_ctor_get(v_cache_3891_, 1);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_add(v_size_3945_, v___x_3947_);
v___x_3949_ = lean_array_get_size(v_keyArray_3946_);
v___x_3950_ = lean_nat_dec_lt(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_dec(v___x_3948_);
lean_dec(v_index_3944_);
goto v___jp_3931_;
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3951_ = lean_unsigned_to_nat(4u);
v___x_3952_ = lean_nat_mul(v___x_3948_, v___x_3951_);
v___x_3953_ = lean_unsigned_to_nat(3u);
v___x_3954_ = lean_nat_mul(v___x_3949_, v___x_3953_);
v___x_3955_ = lean_nat_dec_le(v___x_3952_, v___x_3954_);
lean_dec(v___x_3954_);
lean_dec(v___x_3952_);
if (v___x_3955_ == 0)
{
lean_dec(v___x_3948_);
lean_dec(v_index_3944_);
goto v___jp_3931_;
}
else
{
lean_object* v___x_3956_; 
lean_inc(v_a_3871_);
v___x_3956_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_3891_, v___x_3948_, v_index_3944_, v_e_3381_, v_a_3871_);
lean_dec(v_index_3944_);
v___y_3897_ = v___x_3956_;
goto v___jp_3896_;
}
}
}
default: 
{
lean_object* v_size_3957_; lean_object* v_keyArray_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_size_3957_ = lean_ctor_get(v_cache_3891_, 0);
v_keyArray_3958_ = lean_ctor_get(v_cache_3891_, 1);
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = lean_nat_add(v_size_3957_, v___x_3959_);
v___x_3961_ = lean_array_get_size(v_keyArray_3958_);
v___x_3962_ = lean_nat_dec_lt(v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; 
lean_dec(v___x_3960_);
v___x_3963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3891_);
lean_dec_ref(v_cache_3891_);
v___y_3916_ = v___x_3963_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3964_ = lean_unsigned_to_nat(4u);
v___x_3965_ = lean_nat_mul(v___x_3960_, v___x_3964_);
lean_dec(v___x_3960_);
v___x_3966_ = lean_unsigned_to_nat(3u);
v___x_3967_ = lean_nat_mul(v___x_3961_, v___x_3966_);
v___x_3968_ = lean_nat_dec_le(v___x_3965_, v___x_3967_);
lean_dec(v___x_3967_);
lean_dec(v___x_3965_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3891_);
lean_dec_ref(v_cache_3891_);
v___y_3916_ = v___x_3969_;
goto v___jp_3915_;
}
else
{
v___y_3916_ = v_cache_3891_;
goto v___jp_3915_;
}
}
}
}
v___jp_3896_:
{
lean_object* v___x_3899_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___y_3897_);
v___x_3899_ = v___x_3894_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___y_3897_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_cacheInType_3892_);
v___x_3899_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3901_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 9, v___x_3899_);
v___x_3901_ = v___x_3889_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_share_3877_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_maxFVar_3878_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_proofInstInfo_3879_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_inferType_3880_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v_getLevel_3881_);
lean_ctor_set(v_reuseFailAlloc_3906_, 5, v_congrInfo_3882_);
lean_ctor_set(v_reuseFailAlloc_3906_, 6, v_defEqI_3883_);
lean_ctor_set(v_reuseFailAlloc_3906_, 7, v_extensions_3884_);
lean_ctor_set(v_reuseFailAlloc_3906_, 8, v_issues_3885_);
lean_ctor_set(v_reuseFailAlloc_3906_, 9, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3906_, 10, v_instanceOverrides_3886_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*11, v_debug_3887_);
v___x_3901_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3902_ = lean_st_ref_put(v_a_3384_, v___x_3901_);
if (v_isShared_3874_ == 0)
{
v___x_3904_ = v___x_3873_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3871_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
v___jp_3908_:
{
lean_object* v_size_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_size_3911_ = lean_ctor_get(v___y_3909_, 0);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = lean_nat_add(v_size_3911_, v___x_3912_);
lean_inc(v_a_3871_);
v___x_3914_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3909_, v___x_3913_, v_i_3910_, v_e_3381_, v_a_3871_);
lean_dec(v_i_3910_);
v___y_3897_ = v___x_3914_;
goto v___jp_3896_;
}
v___jp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_3916_, v_e_3381_);
switch(lean_obj_tag(v___x_3917_))
{
case 0:
{
lean_object* v_index_3918_; lean_object* v_size_3919_; lean_object* v___x_3920_; 
v_index_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_index_3918_);
lean_dec_ref_known(v___x_3917_, 3);
v_size_3919_ = lean_ctor_get(v___y_3916_, 0);
lean_inc(v_size_3919_);
lean_inc(v_a_3871_);
v___x_3920_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3916_, v_size_3919_, v_index_3918_, v_e_3381_, v_a_3871_);
lean_dec(v_index_3918_);
v___y_3897_ = v___x_3920_;
goto v___jp_3896_;
}
case 1:
{
lean_object* v_index_3921_; 
v_index_3921_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_index_3921_);
lean_dec_ref_known(v___x_3917_, 1);
v___y_3909_ = v___y_3916_;
v_i_3910_ = v_index_3921_;
goto v___jp_3908_;
}
default: 
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3916_, v___x_3856_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_index_3923_; 
v_index_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_index_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v___y_3909_ = v___y_3916_;
v_i_3910_ = v_index_3923_;
goto v___jp_3908_;
}
else
{
lean_dec_ref_known(v_e_3381_, 4);
v___y_3897_ = v___y_3916_;
goto v___jp_3896_;
}
}
}
}
v___jp_3924_:
{
lean_object* v_size_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_size_3927_ = lean_ctor_get(v___y_3925_, 0);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_size_3927_, v___x_3928_);
lean_inc(v_a_3871_);
v___x_3930_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3925_, v___x_3929_, v_i_3926_, v_e_3381_, v_a_3871_);
lean_dec(v_i_3926_);
v___y_3897_ = v___x_3930_;
goto v___jp_3896_;
}
v___jp_3931_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_3891_);
lean_dec_ref(v_cache_3891_);
v___x_3933_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_3932_, v_e_3381_);
switch(lean_obj_tag(v___x_3933_))
{
case 0:
{
lean_object* v_index_3934_; lean_object* v_size_3935_; lean_object* v___x_3936_; 
v_index_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_index_3934_);
lean_dec_ref_known(v___x_3933_, 3);
v_size_3935_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_size_3935_);
lean_inc(v_a_3871_);
v___x_3936_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3932_, v_size_3935_, v_index_3934_, v_e_3381_, v_a_3871_);
lean_dec(v_index_3934_);
v___y_3897_ = v___x_3936_;
goto v___jp_3896_;
}
case 1:
{
lean_object* v_index_3937_; 
v_index_3937_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_index_3937_);
lean_dec_ref_known(v___x_3933_, 1);
v___y_3925_ = v___x_3932_;
v_i_3926_ = v_index_3937_;
goto v___jp_3924_;
}
default: 
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3932_, v___x_3856_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_index_3939_; 
v_index_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_index_3939_);
lean_dec_ref_known(v___x_3938_, 1);
v___y_3925_ = v___x_3932_;
v_i_3926_ = v_index_3939_;
goto v___jp_3924_;
}
else
{
lean_dec_ref_known(v_e_3381_, 4);
v___y_3897_ = v___x_3932_;
goto v___jp_3896_;
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
lean_dec_ref_known(v_e_3381_, 4);
return v___x_3870_;
}
}
}
else
{
lean_object* v___x_3973_; lean_object* v_canon_3974_; lean_object* v_cacheInType_3975_; lean_object* v___x_3976_; 
v___x_3973_ = lean_st_ref_get(v_a_3384_);
v_canon_3974_ = lean_ctor_get(v___x_3973_, 9);
lean_inc_ref(v_canon_3974_);
lean_dec(v___x_3973_);
v_cacheInType_3975_ = lean_ctor_get(v_canon_3974_, 1);
lean_inc_ref(v_cacheInType_3975_);
lean_dec_ref(v_canon_3974_);
v___x_3976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3975_, v_e_3381_);
lean_dec_ref(v_cacheInType_3975_);
if (lean_obj_tag(v___x_3976_) == 1)
{
lean_object* v_val_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref_known(v_e_3381_, 4);
v_val_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_val_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 0);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_val_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
else
{
lean_object* v___x_3985_; 
lean_dec(v___x_3976_);
lean_inc_ref(v_e_3381_);
v___x_3985_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3857_, v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4087_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_4087_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4087_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v_canon_3991_; lean_object* v_share_3992_; lean_object* v_maxFVar_3993_; lean_object* v_proofInstInfo_3994_; lean_object* v_inferType_3995_; lean_object* v_getLevel_3996_; lean_object* v_congrInfo_3997_; lean_object* v_defEqI_3998_; lean_object* v_extensions_3999_; lean_object* v_issues_4000_; lean_object* v_instanceOverrides_4001_; uint8_t v_debug_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4086_; 
v___x_3990_ = lean_st_ref_take(v_a_3384_);
v_canon_3991_ = lean_ctor_get(v___x_3990_, 9);
v_share_3992_ = lean_ctor_get(v___x_3990_, 0);
v_maxFVar_3993_ = lean_ctor_get(v___x_3990_, 1);
v_proofInstInfo_3994_ = lean_ctor_get(v___x_3990_, 2);
v_inferType_3995_ = lean_ctor_get(v___x_3990_, 3);
v_getLevel_3996_ = lean_ctor_get(v___x_3990_, 4);
v_congrInfo_3997_ = lean_ctor_get(v___x_3990_, 5);
v_defEqI_3998_ = lean_ctor_get(v___x_3990_, 6);
v_extensions_3999_ = lean_ctor_get(v___x_3990_, 7);
v_issues_4000_ = lean_ctor_get(v___x_3990_, 8);
v_instanceOverrides_4001_ = lean_ctor_get(v___x_3990_, 10);
v_debug_4002_ = lean_ctor_get_uint8(v___x_3990_, sizeof(void*)*11);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4004_ = v___x_3990_;
v_isShared_4005_ = v_isSharedCheck_4086_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_instanceOverrides_4001_);
lean_inc(v_canon_3991_);
lean_inc(v_issues_4000_);
lean_inc(v_extensions_3999_);
lean_inc(v_defEqI_3998_);
lean_inc(v_congrInfo_3997_);
lean_inc(v_getLevel_3996_);
lean_inc(v_inferType_3995_);
lean_inc(v_proofInstInfo_3994_);
lean_inc(v_maxFVar_3993_);
lean_inc(v_share_3992_);
lean_dec(v___x_3990_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4086_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_cache_4006_; lean_object* v_cacheInType_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4085_; 
v_cache_4006_ = lean_ctor_get(v_canon_3991_, 0);
v_cacheInType_4007_ = lean_ctor_get(v_canon_3991_, 1);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_canon_3991_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4009_ = v_canon_3991_;
v_isShared_4010_ = v_isSharedCheck_4085_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_cacheInType_4007_);
lean_inc(v_cache_4006_);
lean_dec(v_canon_3991_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4085_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___y_4012_; lean_object* v___y_4024_; lean_object* v_i_4025_; lean_object* v___y_4040_; lean_object* v_i_4041_; lean_object* v___y_4047_; lean_object* v___x_4055_; 
v___x_4055_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_4007_, v_e_3381_);
switch(lean_obj_tag(v___x_4055_))
{
case 0:
{
lean_object* v_index_4056_; lean_object* v_size_4057_; lean_object* v___x_4058_; 
v_index_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_index_4056_);
lean_dec_ref_known(v___x_4055_, 3);
v_size_4057_ = lean_ctor_get(v_cacheInType_4007_, 0);
lean_inc(v_size_4057_);
lean_inc(v_a_3986_);
v___x_4058_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4007_, v_size_4057_, v_index_4056_, v_e_3381_, v_a_3986_);
lean_dec(v_index_4056_);
v___y_4012_ = v___x_4058_;
goto v___jp_4011_;
}
case 1:
{
lean_object* v_index_4059_; lean_object* v_size_4060_; lean_object* v_keyArray_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_index_4059_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_index_4059_);
lean_dec_ref_known(v___x_4055_, 1);
v_size_4060_ = lean_ctor_get(v_cacheInType_4007_, 0);
v_keyArray_4061_ = lean_ctor_get(v_cacheInType_4007_, 1);
v___x_4062_ = lean_unsigned_to_nat(1u);
v___x_4063_ = lean_nat_add(v_size_4060_, v___x_4062_);
v___x_4064_ = lean_array_get_size(v_keyArray_4061_);
v___x_4065_ = lean_nat_dec_lt(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
lean_dec(v___x_4063_);
lean_dec(v_index_4059_);
goto v___jp_4030_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4066_ = lean_unsigned_to_nat(4u);
v___x_4067_ = lean_nat_mul(v___x_4063_, v___x_4066_);
v___x_4068_ = lean_unsigned_to_nat(3u);
v___x_4069_ = lean_nat_mul(v___x_4064_, v___x_4068_);
v___x_4070_ = lean_nat_dec_le(v___x_4067_, v___x_4069_);
lean_dec(v___x_4069_);
lean_dec(v___x_4067_);
if (v___x_4070_ == 0)
{
lean_dec(v___x_4063_);
lean_dec(v_index_4059_);
goto v___jp_4030_;
}
else
{
lean_object* v___x_4071_; 
lean_inc(v_a_3986_);
v___x_4071_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4007_, v___x_4063_, v_index_4059_, v_e_3381_, v_a_3986_);
lean_dec(v_index_4059_);
v___y_4012_ = v___x_4071_;
goto v___jp_4011_;
}
}
}
default: 
{
lean_object* v_size_4072_; lean_object* v_keyArray_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_size_4072_ = lean_ctor_get(v_cacheInType_4007_, 0);
v_keyArray_4073_ = lean_ctor_get(v_cacheInType_4007_, 1);
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = lean_nat_add(v_size_4072_, v___x_4074_);
v___x_4076_ = lean_array_get_size(v_keyArray_4073_);
v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
lean_dec(v___x_4075_);
v___x_4078_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4007_);
lean_dec_ref(v_cacheInType_4007_);
v___y_4047_ = v___x_4078_;
goto v___jp_4046_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
v___x_4079_ = lean_unsigned_to_nat(4u);
v___x_4080_ = lean_nat_mul(v___x_4075_, v___x_4079_);
lean_dec(v___x_4075_);
v___x_4081_ = lean_unsigned_to_nat(3u);
v___x_4082_ = lean_nat_mul(v___x_4076_, v___x_4081_);
v___x_4083_ = lean_nat_dec_le(v___x_4080_, v___x_4082_);
lean_dec(v___x_4082_);
lean_dec(v___x_4080_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4007_);
lean_dec_ref(v_cacheInType_4007_);
v___y_4047_ = v___x_4084_;
goto v___jp_4046_;
}
else
{
v___y_4047_ = v_cacheInType_4007_;
goto v___jp_4046_;
}
}
}
}
v___jp_4011_:
{
lean_object* v___x_4014_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___y_4012_);
v___x_4014_ = v___x_4009_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_cache_4006_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___y_4012_);
v___x_4014_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4016_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 9, v___x_4014_);
v___x_4016_ = v___x_4004_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_share_3992_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_maxFVar_3993_);
lean_ctor_set(v_reuseFailAlloc_4021_, 2, v_proofInstInfo_3994_);
lean_ctor_set(v_reuseFailAlloc_4021_, 3, v_inferType_3995_);
lean_ctor_set(v_reuseFailAlloc_4021_, 4, v_getLevel_3996_);
lean_ctor_set(v_reuseFailAlloc_4021_, 5, v_congrInfo_3997_);
lean_ctor_set(v_reuseFailAlloc_4021_, 6, v_defEqI_3998_);
lean_ctor_set(v_reuseFailAlloc_4021_, 7, v_extensions_3999_);
lean_ctor_set(v_reuseFailAlloc_4021_, 8, v_issues_4000_);
lean_ctor_set(v_reuseFailAlloc_4021_, 9, v___x_4014_);
lean_ctor_set(v_reuseFailAlloc_4021_, 10, v_instanceOverrides_4001_);
lean_ctor_set_uint8(v_reuseFailAlloc_4021_, sizeof(void*)*11, v_debug_4002_);
v___x_4016_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4017_ = lean_st_ref_put(v_a_3384_, v___x_4016_);
if (v_isShared_3989_ == 0)
{
v___x_4019_ = v___x_3988_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_3986_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
v___jp_4023_:
{
lean_object* v_size_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_size_4026_ = lean_ctor_get(v___y_4024_, 0);
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_add(v_size_4026_, v___x_4027_);
lean_inc(v_a_3986_);
v___x_4029_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4024_, v___x_4028_, v_i_4025_, v_e_3381_, v_a_3986_);
lean_dec(v_i_4025_);
v___y_4012_ = v___x_4029_;
goto v___jp_4011_;
}
v___jp_4030_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4007_);
lean_dec_ref(v_cacheInType_4007_);
v___x_4032_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_4031_, v_e_3381_);
switch(lean_obj_tag(v___x_4032_))
{
case 0:
{
lean_object* v_index_4033_; lean_object* v_size_4034_; lean_object* v___x_4035_; 
v_index_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_index_4033_);
lean_dec_ref_known(v___x_4032_, 3);
v_size_4034_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_size_4034_);
lean_inc(v_a_3986_);
v___x_4035_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4031_, v_size_4034_, v_index_4033_, v_e_3381_, v_a_3986_);
lean_dec(v_index_4033_);
v___y_4012_ = v___x_4035_;
goto v___jp_4011_;
}
case 1:
{
lean_object* v_index_4036_; 
v_index_4036_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_index_4036_);
lean_dec_ref_known(v___x_4032_, 1);
v___y_4024_ = v___x_4031_;
v_i_4025_ = v_index_4036_;
goto v___jp_4023_;
}
default: 
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4031_, v___x_3856_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_index_4038_; 
v_index_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_index_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___y_4024_ = v___x_4031_;
v_i_4025_ = v_index_4038_;
goto v___jp_4023_;
}
else
{
lean_dec_ref_known(v_e_3381_, 4);
v___y_4012_ = v___x_4031_;
goto v___jp_4011_;
}
}
}
}
v___jp_4039_:
{
lean_object* v_size_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_size_4042_ = lean_ctor_get(v___y_4040_, 0);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = lean_nat_add(v_size_4042_, v___x_4043_);
lean_inc(v_a_3986_);
v___x_4045_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4040_, v___x_4044_, v_i_4041_, v_e_3381_, v_a_3986_);
lean_dec(v_i_4041_);
v___y_4012_ = v___x_4045_;
goto v___jp_4011_;
}
v___jp_4046_:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_4047_, v_e_3381_);
switch(lean_obj_tag(v___x_4048_))
{
case 0:
{
lean_object* v_index_4049_; lean_object* v_size_4050_; lean_object* v___x_4051_; 
v_index_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_index_4049_);
lean_dec_ref_known(v___x_4048_, 3);
v_size_4050_ = lean_ctor_get(v___y_4047_, 0);
lean_inc(v_size_4050_);
lean_inc(v_a_3986_);
v___x_4051_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4047_, v_size_4050_, v_index_4049_, v_e_3381_, v_a_3986_);
lean_dec(v_index_4049_);
v___y_4012_ = v___x_4051_;
goto v___jp_4011_;
}
case 1:
{
lean_object* v_index_4052_; 
v_index_4052_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_index_4052_);
lean_dec_ref_known(v___x_4048_, 1);
v___y_4040_ = v___y_4047_;
v_i_4041_ = v_index_4052_;
goto v___jp_4039_;
}
default: 
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4047_, v___x_3856_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_index_4054_; 
v_index_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_index_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___y_4040_ = v___y_4047_;
v_i_4041_ = v_index_4054_;
goto v___jp_4039_;
}
else
{
lean_dec_ref_known(v_e_3381_, 4);
v___y_4012_ = v___y_4047_;
goto v___jp_4011_;
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
lean_dec_ref_known(v_e_3381_, 4);
return v___x_3985_;
}
}
}
}
case 5:
{
if (v_a_3382_ == 0)
{
lean_object* v___x_4088_; lean_object* v_canon_4089_; lean_object* v_cache_4090_; lean_object* v___x_4091_; 
v___x_4088_ = lean_st_ref_get(v_a_3384_);
v_canon_4089_ = lean_ctor_get(v___x_4088_, 9);
lean_inc_ref(v_canon_4089_);
lean_dec(v___x_4088_);
v_cache_4090_ = lean_ctor_get(v_canon_4089_, 0);
lean_inc_ref(v_cache_4090_);
lean_dec_ref(v_canon_4089_);
v___x_4091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_4090_, v_e_3381_);
lean_dec_ref(v_cache_4090_);
if (lean_obj_tag(v___x_4091_) == 1)
{
lean_object* v_val_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref_known(v_e_3381_, 2);
v_val_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_val_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 0);
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_val_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
else
{
lean_object* v___x_4100_; 
lean_dec(v___x_4091_);
lean_inc_ref(v_e_3381_);
v___x_4100_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4204_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4204_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4204_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; lean_object* v_canon_4106_; lean_object* v_share_4107_; lean_object* v_maxFVar_4108_; lean_object* v_proofInstInfo_4109_; lean_object* v_inferType_4110_; lean_object* v_getLevel_4111_; lean_object* v_congrInfo_4112_; lean_object* v_defEqI_4113_; lean_object* v_extensions_4114_; lean_object* v_issues_4115_; lean_object* v_instanceOverrides_4116_; uint8_t v_debug_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4203_; 
v___x_4105_ = lean_st_ref_take(v_a_3384_);
v_canon_4106_ = lean_ctor_get(v___x_4105_, 9);
v_share_4107_ = lean_ctor_get(v___x_4105_, 0);
v_maxFVar_4108_ = lean_ctor_get(v___x_4105_, 1);
v_proofInstInfo_4109_ = lean_ctor_get(v___x_4105_, 2);
v_inferType_4110_ = lean_ctor_get(v___x_4105_, 3);
v_getLevel_4111_ = lean_ctor_get(v___x_4105_, 4);
v_congrInfo_4112_ = lean_ctor_get(v___x_4105_, 5);
v_defEqI_4113_ = lean_ctor_get(v___x_4105_, 6);
v_extensions_4114_ = lean_ctor_get(v___x_4105_, 7);
v_issues_4115_ = lean_ctor_get(v___x_4105_, 8);
v_instanceOverrides_4116_ = lean_ctor_get(v___x_4105_, 10);
v_debug_4117_ = lean_ctor_get_uint8(v___x_4105_, sizeof(void*)*11);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4119_ = v___x_4105_;
v_isShared_4120_ = v_isSharedCheck_4203_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_instanceOverrides_4116_);
lean_inc(v_canon_4106_);
lean_inc(v_issues_4115_);
lean_inc(v_extensions_4114_);
lean_inc(v_defEqI_4113_);
lean_inc(v_congrInfo_4112_);
lean_inc(v_getLevel_4111_);
lean_inc(v_inferType_4110_);
lean_inc(v_proofInstInfo_4109_);
lean_inc(v_maxFVar_4108_);
lean_inc(v_share_4107_);
lean_dec(v___x_4105_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4203_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v_cache_4121_; lean_object* v_cacheInType_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4202_; 
v_cache_4121_ = lean_ctor_get(v_canon_4106_, 0);
v_cacheInType_4122_ = lean_ctor_get(v_canon_4106_, 1);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_canon_4106_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4124_ = v_canon_4106_;
v_isShared_4125_ = v_isSharedCheck_4202_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_cacheInType_4122_);
lean_inc(v_cache_4121_);
lean_dec(v_canon_4106_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4202_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___y_4127_; lean_object* v___y_4139_; lean_object* v_i_4140_; lean_object* v___y_4146_; lean_object* v___y_4156_; lean_object* v_i_4157_; lean_object* v___x_4172_; 
v___x_4172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_4121_, v_e_3381_);
switch(lean_obj_tag(v___x_4172_))
{
case 0:
{
lean_object* v_index_4173_; lean_object* v_size_4174_; lean_object* v___x_4175_; 
v_index_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_index_4173_);
lean_dec_ref_known(v___x_4172_, 3);
v_size_4174_ = lean_ctor_get(v_cache_4121_, 0);
lean_inc(v_size_4174_);
lean_inc(v_a_4101_);
v___x_4175_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_4121_, v_size_4174_, v_index_4173_, v_e_3381_, v_a_4101_);
lean_dec(v_index_4173_);
v___y_4127_ = v___x_4175_;
goto v___jp_4126_;
}
case 1:
{
lean_object* v_index_4176_; lean_object* v_size_4177_; lean_object* v_keyArray_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v_index_4176_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_index_4176_);
lean_dec_ref_known(v___x_4172_, 1);
v_size_4177_ = lean_ctor_get(v_cache_4121_, 0);
v_keyArray_4178_ = lean_ctor_get(v_cache_4121_, 1);
v___x_4179_ = lean_unsigned_to_nat(1u);
v___x_4180_ = lean_nat_add(v_size_4177_, v___x_4179_);
v___x_4181_ = lean_array_get_size(v_keyArray_4178_);
v___x_4182_ = lean_nat_dec_lt(v___x_4180_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_dec(v___x_4180_);
lean_dec(v_index_4176_);
goto v___jp_4162_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v___x_4183_ = lean_unsigned_to_nat(4u);
v___x_4184_ = lean_nat_mul(v___x_4180_, v___x_4183_);
v___x_4185_ = lean_unsigned_to_nat(3u);
v___x_4186_ = lean_nat_mul(v___x_4181_, v___x_4185_);
v___x_4187_ = lean_nat_dec_le(v___x_4184_, v___x_4186_);
lean_dec(v___x_4186_);
lean_dec(v___x_4184_);
if (v___x_4187_ == 0)
{
lean_dec(v___x_4180_);
lean_dec(v_index_4176_);
goto v___jp_4162_;
}
else
{
lean_object* v___x_4188_; 
lean_inc(v_a_4101_);
v___x_4188_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_4121_, v___x_4180_, v_index_4176_, v_e_3381_, v_a_4101_);
lean_dec(v_index_4176_);
v___y_4127_ = v___x_4188_;
goto v___jp_4126_;
}
}
}
default: 
{
lean_object* v_size_4189_; lean_object* v_keyArray_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v_size_4189_ = lean_ctor_get(v_cache_4121_, 0);
v_keyArray_4190_ = lean_ctor_get(v_cache_4121_, 1);
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_add(v_size_4189_, v___x_4191_);
v___x_4193_ = lean_array_get_size(v_keyArray_4190_);
v___x_4194_ = lean_nat_dec_lt(v___x_4192_, v___x_4193_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; 
lean_dec(v___x_4192_);
v___x_4195_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4121_);
lean_dec_ref(v_cache_4121_);
v___y_4146_ = v___x_4195_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4196_ = lean_unsigned_to_nat(4u);
v___x_4197_ = lean_nat_mul(v___x_4192_, v___x_4196_);
lean_dec(v___x_4192_);
v___x_4198_ = lean_unsigned_to_nat(3u);
v___x_4199_ = lean_nat_mul(v___x_4193_, v___x_4198_);
v___x_4200_ = lean_nat_dec_le(v___x_4197_, v___x_4199_);
lean_dec(v___x_4199_);
lean_dec(v___x_4197_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4121_);
lean_dec_ref(v_cache_4121_);
v___y_4146_ = v___x_4201_;
goto v___jp_4145_;
}
else
{
v___y_4146_ = v_cache_4121_;
goto v___jp_4145_;
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4129_; 
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___y_4127_);
v___x_4129_ = v___x_4124_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___y_4127_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_cacheInType_4122_);
v___x_4129_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 9, v___x_4129_);
v___x_4131_ = v___x_4119_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_share_4107_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_maxFVar_4108_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_proofInstInfo_4109_);
lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_inferType_4110_);
lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_getLevel_4111_);
lean_ctor_set(v_reuseFailAlloc_4136_, 5, v_congrInfo_4112_);
lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_defEqI_4113_);
lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_extensions_4114_);
lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_issues_4115_);
lean_ctor_set(v_reuseFailAlloc_4136_, 9, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4136_, 10, v_instanceOverrides_4116_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*11, v_debug_4117_);
v___x_4131_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4132_ = lean_st_ref_put(v_a_3384_, v___x_4131_);
if (v_isShared_4104_ == 0)
{
v___x_4134_ = v___x_4103_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4101_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
v___jp_4138_:
{
lean_object* v_size_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_size_4141_ = lean_ctor_get(v___y_4139_, 0);
v___x_4142_ = lean_unsigned_to_nat(1u);
v___x_4143_ = lean_nat_add(v_size_4141_, v___x_4142_);
lean_inc(v_a_4101_);
v___x_4144_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4139_, v___x_4143_, v_i_4140_, v_e_3381_, v_a_4101_);
lean_dec(v_i_4140_);
v___y_4127_ = v___x_4144_;
goto v___jp_4126_;
}
v___jp_4145_:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_4146_, v_e_3381_);
switch(lean_obj_tag(v___x_4147_))
{
case 0:
{
lean_object* v_index_4148_; lean_object* v_size_4149_; lean_object* v___x_4150_; 
v_index_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_index_4148_);
lean_dec_ref_known(v___x_4147_, 3);
v_size_4149_ = lean_ctor_get(v___y_4146_, 0);
lean_inc(v_size_4149_);
lean_inc(v_a_4101_);
v___x_4150_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4146_, v_size_4149_, v_index_4148_, v_e_3381_, v_a_4101_);
lean_dec(v_index_4148_);
v___y_4127_ = v___x_4150_;
goto v___jp_4126_;
}
case 1:
{
lean_object* v_index_4151_; 
v_index_4151_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_index_4151_);
lean_dec_ref_known(v___x_4147_, 1);
v___y_4139_ = v___y_4146_;
v_i_4140_ = v_index_4151_;
goto v___jp_4138_;
}
default: 
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4146_, v___x_4152_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_index_4154_; 
v_index_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_index_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4139_ = v___y_4146_;
v_i_4140_ = v_index_4154_;
goto v___jp_4138_;
}
else
{
lean_dec_ref_known(v_e_3381_, 2);
v___y_4127_ = v___y_4146_;
goto v___jp_4126_;
}
}
}
}
v___jp_4155_:
{
lean_object* v_size_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v_size_4158_ = lean_ctor_get(v___y_4156_, 0);
v___x_4159_ = lean_unsigned_to_nat(1u);
v___x_4160_ = lean_nat_add(v_size_4158_, v___x_4159_);
lean_inc(v_a_4101_);
v___x_4161_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4156_, v___x_4160_, v_i_4157_, v_e_3381_, v_a_4101_);
lean_dec(v_i_4157_);
v___y_4127_ = v___x_4161_;
goto v___jp_4126_;
}
v___jp_4162_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4121_);
lean_dec_ref(v_cache_4121_);
v___x_4164_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_4163_, v_e_3381_);
switch(lean_obj_tag(v___x_4164_))
{
case 0:
{
lean_object* v_index_4165_; lean_object* v_size_4166_; lean_object* v___x_4167_; 
v_index_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_index_4165_);
lean_dec_ref_known(v___x_4164_, 3);
v_size_4166_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_size_4166_);
lean_inc(v_a_4101_);
v___x_4167_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4163_, v_size_4166_, v_index_4165_, v_e_3381_, v_a_4101_);
lean_dec(v_index_4165_);
v___y_4127_ = v___x_4167_;
goto v___jp_4126_;
}
case 1:
{
lean_object* v_index_4168_; 
v_index_4168_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_index_4168_);
lean_dec_ref_known(v___x_4164_, 1);
v___y_4156_ = v___x_4163_;
v_i_4157_ = v_index_4168_;
goto v___jp_4155_;
}
default: 
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4163_, v___x_4169_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_index_4171_; 
v_index_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_index_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___y_4156_ = v___x_4163_;
v_i_4157_ = v_index_4171_;
goto v___jp_4155_;
}
else
{
lean_dec_ref_known(v_e_3381_, 2);
v___y_4127_ = v___x_4163_;
goto v___jp_4126_;
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
lean_dec_ref_known(v_e_3381_, 2);
return v___x_4100_;
}
}
}
else
{
lean_object* v___x_4205_; lean_object* v_canon_4206_; lean_object* v_cacheInType_4207_; lean_object* v___x_4208_; 
v___x_4205_ = lean_st_ref_get(v_a_3384_);
v_canon_4206_ = lean_ctor_get(v___x_4205_, 9);
lean_inc_ref(v_canon_4206_);
lean_dec(v___x_4205_);
v_cacheInType_4207_ = lean_ctor_get(v_canon_4206_, 1);
lean_inc_ref(v_cacheInType_4207_);
lean_dec_ref(v_canon_4206_);
v___x_4208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_4207_, v_e_3381_);
lean_dec_ref(v_cacheInType_4207_);
if (lean_obj_tag(v___x_4208_) == 1)
{
lean_object* v_val_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref_known(v_e_3381_, 2);
v_val_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_val_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 0);
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_val_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
else
{
lean_object* v___x_4217_; 
lean_dec(v___x_4208_);
lean_inc_ref(v_e_3381_);
v___x_4217_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4321_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4321_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4321_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v_canon_4223_; lean_object* v_share_4224_; lean_object* v_maxFVar_4225_; lean_object* v_proofInstInfo_4226_; lean_object* v_inferType_4227_; lean_object* v_getLevel_4228_; lean_object* v_congrInfo_4229_; lean_object* v_defEqI_4230_; lean_object* v_extensions_4231_; lean_object* v_issues_4232_; lean_object* v_instanceOverrides_4233_; uint8_t v_debug_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4320_; 
v___x_4222_ = lean_st_ref_take(v_a_3384_);
v_canon_4223_ = lean_ctor_get(v___x_4222_, 9);
v_share_4224_ = lean_ctor_get(v___x_4222_, 0);
v_maxFVar_4225_ = lean_ctor_get(v___x_4222_, 1);
v_proofInstInfo_4226_ = lean_ctor_get(v___x_4222_, 2);
v_inferType_4227_ = lean_ctor_get(v___x_4222_, 3);
v_getLevel_4228_ = lean_ctor_get(v___x_4222_, 4);
v_congrInfo_4229_ = lean_ctor_get(v___x_4222_, 5);
v_defEqI_4230_ = lean_ctor_get(v___x_4222_, 6);
v_extensions_4231_ = lean_ctor_get(v___x_4222_, 7);
v_issues_4232_ = lean_ctor_get(v___x_4222_, 8);
v_instanceOverrides_4233_ = lean_ctor_get(v___x_4222_, 10);
v_debug_4234_ = lean_ctor_get_uint8(v___x_4222_, sizeof(void*)*11);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4236_ = v___x_4222_;
v_isShared_4237_ = v_isSharedCheck_4320_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_instanceOverrides_4233_);
lean_inc(v_canon_4223_);
lean_inc(v_issues_4232_);
lean_inc(v_extensions_4231_);
lean_inc(v_defEqI_4230_);
lean_inc(v_congrInfo_4229_);
lean_inc(v_getLevel_4228_);
lean_inc(v_inferType_4227_);
lean_inc(v_proofInstInfo_4226_);
lean_inc(v_maxFVar_4225_);
lean_inc(v_share_4224_);
lean_dec(v___x_4222_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4320_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v_cache_4238_; lean_object* v_cacheInType_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4319_; 
v_cache_4238_ = lean_ctor_get(v_canon_4223_, 0);
v_cacheInType_4239_ = lean_ctor_get(v_canon_4223_, 1);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_canon_4223_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4241_ = v_canon_4223_;
v_isShared_4242_ = v_isSharedCheck_4319_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_cacheInType_4239_);
lean_inc(v_cache_4238_);
lean_dec(v_canon_4223_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4319_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___y_4244_; lean_object* v___y_4256_; lean_object* v_i_4257_; lean_object* v___y_4273_; lean_object* v_i_4274_; lean_object* v___y_4280_; lean_object* v___x_4289_; 
v___x_4289_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_4239_, v_e_3381_);
switch(lean_obj_tag(v___x_4289_))
{
case 0:
{
lean_object* v_index_4290_; lean_object* v_size_4291_; lean_object* v___x_4292_; 
v_index_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_index_4290_);
lean_dec_ref_known(v___x_4289_, 3);
v_size_4291_ = lean_ctor_get(v_cacheInType_4239_, 0);
lean_inc(v_size_4291_);
lean_inc(v_a_4218_);
v___x_4292_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4239_, v_size_4291_, v_index_4290_, v_e_3381_, v_a_4218_);
lean_dec(v_index_4290_);
v___y_4244_ = v___x_4292_;
goto v___jp_4243_;
}
case 1:
{
lean_object* v_index_4293_; lean_object* v_size_4294_; lean_object* v_keyArray_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_index_4293_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_index_4293_);
lean_dec_ref_known(v___x_4289_, 1);
v_size_4294_ = lean_ctor_get(v_cacheInType_4239_, 0);
v_keyArray_4295_ = lean_ctor_get(v_cacheInType_4239_, 1);
v___x_4296_ = lean_unsigned_to_nat(1u);
v___x_4297_ = lean_nat_add(v_size_4294_, v___x_4296_);
v___x_4298_ = lean_array_get_size(v_keyArray_4295_);
v___x_4299_ = lean_nat_dec_lt(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_dec(v___x_4297_);
lean_dec(v_index_4293_);
goto v___jp_4262_;
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4300_ = lean_unsigned_to_nat(4u);
v___x_4301_ = lean_nat_mul(v___x_4297_, v___x_4300_);
v___x_4302_ = lean_unsigned_to_nat(3u);
v___x_4303_ = lean_nat_mul(v___x_4298_, v___x_4302_);
v___x_4304_ = lean_nat_dec_le(v___x_4301_, v___x_4303_);
lean_dec(v___x_4303_);
lean_dec(v___x_4301_);
if (v___x_4304_ == 0)
{
lean_dec(v___x_4297_);
lean_dec(v_index_4293_);
goto v___jp_4262_;
}
else
{
lean_object* v___x_4305_; 
lean_inc(v_a_4218_);
v___x_4305_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4239_, v___x_4297_, v_index_4293_, v_e_3381_, v_a_4218_);
lean_dec(v_index_4293_);
v___y_4244_ = v___x_4305_;
goto v___jp_4243_;
}
}
}
default: 
{
lean_object* v_size_4306_; lean_object* v_keyArray_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v_size_4306_ = lean_ctor_get(v_cacheInType_4239_, 0);
v_keyArray_4307_ = lean_ctor_get(v_cacheInType_4239_, 1);
v___x_4308_ = lean_unsigned_to_nat(1u);
v___x_4309_ = lean_nat_add(v_size_4306_, v___x_4308_);
v___x_4310_ = lean_array_get_size(v_keyArray_4307_);
v___x_4311_ = lean_nat_dec_lt(v___x_4309_, v___x_4310_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; 
lean_dec(v___x_4309_);
v___x_4312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4239_);
lean_dec_ref(v_cacheInType_4239_);
v___y_4280_ = v___x_4312_;
goto v___jp_4279_;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4313_ = lean_unsigned_to_nat(4u);
v___x_4314_ = lean_nat_mul(v___x_4309_, v___x_4313_);
lean_dec(v___x_4309_);
v___x_4315_ = lean_unsigned_to_nat(3u);
v___x_4316_ = lean_nat_mul(v___x_4310_, v___x_4315_);
v___x_4317_ = lean_nat_dec_le(v___x_4314_, v___x_4316_);
lean_dec(v___x_4316_);
lean_dec(v___x_4314_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4239_);
lean_dec_ref(v_cacheInType_4239_);
v___y_4280_ = v___x_4318_;
goto v___jp_4279_;
}
else
{
v___y_4280_ = v_cacheInType_4239_;
goto v___jp_4279_;
}
}
}
}
v___jp_4243_:
{
lean_object* v___x_4246_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 1, v___y_4244_);
v___x_4246_ = v___x_4241_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_cache_4238_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___y_4244_);
v___x_4246_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4248_; 
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 9, v___x_4246_);
v___x_4248_ = v___x_4236_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_share_4224_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_maxFVar_4225_);
lean_ctor_set(v_reuseFailAlloc_4253_, 2, v_proofInstInfo_4226_);
lean_ctor_set(v_reuseFailAlloc_4253_, 3, v_inferType_4227_);
lean_ctor_set(v_reuseFailAlloc_4253_, 4, v_getLevel_4228_);
lean_ctor_set(v_reuseFailAlloc_4253_, 5, v_congrInfo_4229_);
lean_ctor_set(v_reuseFailAlloc_4253_, 6, v_defEqI_4230_);
lean_ctor_set(v_reuseFailAlloc_4253_, 7, v_extensions_4231_);
lean_ctor_set(v_reuseFailAlloc_4253_, 8, v_issues_4232_);
lean_ctor_set(v_reuseFailAlloc_4253_, 9, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4253_, 10, v_instanceOverrides_4233_);
lean_ctor_set_uint8(v_reuseFailAlloc_4253_, sizeof(void*)*11, v_debug_4234_);
v___x_4248_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4249_ = lean_st_ref_put(v_a_3384_, v___x_4248_);
if (v_isShared_4221_ == 0)
{
v___x_4251_ = v___x_4220_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4218_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
v___jp_4255_:
{
lean_object* v_size_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_size_4258_ = lean_ctor_get(v___y_4256_, 0);
v___x_4259_ = lean_unsigned_to_nat(1u);
v___x_4260_ = lean_nat_add(v_size_4258_, v___x_4259_);
lean_inc(v_a_4218_);
v___x_4261_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4256_, v___x_4260_, v_i_4257_, v_e_3381_, v_a_4218_);
lean_dec(v_i_4257_);
v___y_4244_ = v___x_4261_;
goto v___jp_4243_;
}
v___jp_4262_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4239_);
lean_dec_ref(v_cacheInType_4239_);
v___x_4264_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_4263_, v_e_3381_);
switch(lean_obj_tag(v___x_4264_))
{
case 0:
{
lean_object* v_index_4265_; lean_object* v_size_4266_; lean_object* v___x_4267_; 
v_index_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_index_4265_);
lean_dec_ref_known(v___x_4264_, 3);
v_size_4266_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_size_4266_);
lean_inc(v_a_4218_);
v___x_4267_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4263_, v_size_4266_, v_index_4265_, v_e_3381_, v_a_4218_);
lean_dec(v_index_4265_);
v___y_4244_ = v___x_4267_;
goto v___jp_4243_;
}
case 1:
{
lean_object* v_index_4268_; 
v_index_4268_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_index_4268_);
lean_dec_ref_known(v___x_4264_, 1);
v___y_4256_ = v___x_4263_;
v_i_4257_ = v_index_4268_;
goto v___jp_4255_;
}
default: 
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4263_, v___x_4269_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_index_4271_; 
v_index_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_index_4271_);
lean_dec_ref_known(v___x_4270_, 1);
v___y_4256_ = v___x_4263_;
v_i_4257_ = v_index_4271_;
goto v___jp_4255_;
}
else
{
lean_dec_ref_known(v_e_3381_, 2);
v___y_4244_ = v___x_4263_;
goto v___jp_4243_;
}
}
}
}
v___jp_4272_:
{
lean_object* v_size_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v_size_4275_ = lean_ctor_get(v___y_4273_, 0);
v___x_4276_ = lean_unsigned_to_nat(1u);
v___x_4277_ = lean_nat_add(v_size_4275_, v___x_4276_);
lean_inc(v_a_4218_);
v___x_4278_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4273_, v___x_4277_, v_i_4274_, v_e_3381_, v_a_4218_);
lean_dec(v_i_4274_);
v___y_4244_ = v___x_4278_;
goto v___jp_4243_;
}
v___jp_4279_:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_4280_, v_e_3381_);
switch(lean_obj_tag(v___x_4281_))
{
case 0:
{
lean_object* v_index_4282_; lean_object* v_size_4283_; lean_object* v___x_4284_; 
v_index_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_index_4282_);
lean_dec_ref_known(v___x_4281_, 3);
v_size_4283_ = lean_ctor_get(v___y_4280_, 0);
lean_inc(v_size_4283_);
lean_inc(v_a_4218_);
v___x_4284_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4280_, v_size_4283_, v_index_4282_, v_e_3381_, v_a_4218_);
lean_dec(v_index_4282_);
v___y_4244_ = v___x_4284_;
goto v___jp_4243_;
}
case 1:
{
lean_object* v_index_4285_; 
v_index_4285_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_index_4285_);
lean_dec_ref_known(v___x_4281_, 1);
v___y_4273_ = v___y_4280_;
v_i_4274_ = v_index_4285_;
goto v___jp_4272_;
}
default: 
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4280_, v___x_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_index_4288_; 
v_index_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_index_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___y_4273_ = v___y_4280_;
v_i_4274_ = v_index_4288_;
goto v___jp_4272_;
}
else
{
lean_dec_ref_known(v_e_3381_, 2);
v___y_4244_ = v___y_4280_;
goto v___jp_4243_;
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
lean_dec_ref_known(v_e_3381_, 2);
return v___x_4217_;
}
}
}
}
case 11:
{
if (v_a_3382_ == 0)
{
lean_object* v___x_4322_; lean_object* v_canon_4323_; lean_object* v_cache_4324_; lean_object* v___x_4325_; 
v___x_4322_ = lean_st_ref_get(v_a_3384_);
v_canon_4323_ = lean_ctor_get(v___x_4322_, 9);
lean_inc_ref(v_canon_4323_);
lean_dec(v___x_4322_);
v_cache_4324_ = lean_ctor_get(v_canon_4323_, 0);
lean_inc_ref(v_cache_4324_);
lean_dec_ref(v_canon_4323_);
v___x_4325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_4324_, v_e_3381_);
lean_dec_ref(v_cache_4324_);
if (lean_obj_tag(v___x_4325_) == 1)
{
lean_object* v_val_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_val_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 0);
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_val_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v___x_4334_; 
lean_dec(v___x_4325_);
lean_inc_ref(v_e_3381_);
v___x_4334_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4438_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4438_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4438_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4339_; lean_object* v_canon_4340_; lean_object* v_share_4341_; lean_object* v_maxFVar_4342_; lean_object* v_proofInstInfo_4343_; lean_object* v_inferType_4344_; lean_object* v_getLevel_4345_; lean_object* v_congrInfo_4346_; lean_object* v_defEqI_4347_; lean_object* v_extensions_4348_; lean_object* v_issues_4349_; lean_object* v_instanceOverrides_4350_; uint8_t v_debug_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4437_; 
v___x_4339_ = lean_st_ref_take(v_a_3384_);
v_canon_4340_ = lean_ctor_get(v___x_4339_, 9);
v_share_4341_ = lean_ctor_get(v___x_4339_, 0);
v_maxFVar_4342_ = lean_ctor_get(v___x_4339_, 1);
v_proofInstInfo_4343_ = lean_ctor_get(v___x_4339_, 2);
v_inferType_4344_ = lean_ctor_get(v___x_4339_, 3);
v_getLevel_4345_ = lean_ctor_get(v___x_4339_, 4);
v_congrInfo_4346_ = lean_ctor_get(v___x_4339_, 5);
v_defEqI_4347_ = lean_ctor_get(v___x_4339_, 6);
v_extensions_4348_ = lean_ctor_get(v___x_4339_, 7);
v_issues_4349_ = lean_ctor_get(v___x_4339_, 8);
v_instanceOverrides_4350_ = lean_ctor_get(v___x_4339_, 10);
v_debug_4351_ = lean_ctor_get_uint8(v___x_4339_, sizeof(void*)*11);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4353_ = v___x_4339_;
v_isShared_4354_ = v_isSharedCheck_4437_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_instanceOverrides_4350_);
lean_inc(v_canon_4340_);
lean_inc(v_issues_4349_);
lean_inc(v_extensions_4348_);
lean_inc(v_defEqI_4347_);
lean_inc(v_congrInfo_4346_);
lean_inc(v_getLevel_4345_);
lean_inc(v_inferType_4344_);
lean_inc(v_proofInstInfo_4343_);
lean_inc(v_maxFVar_4342_);
lean_inc(v_share_4341_);
lean_dec(v___x_4339_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4437_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_cache_4355_; lean_object* v_cacheInType_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4436_; 
v_cache_4355_ = lean_ctor_get(v_canon_4340_, 0);
v_cacheInType_4356_ = lean_ctor_get(v_canon_4340_, 1);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_canon_4340_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4358_ = v_canon_4340_;
v_isShared_4359_ = v_isSharedCheck_4436_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_cacheInType_4356_);
lean_inc(v_cache_4355_);
lean_dec(v_canon_4340_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4436_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___y_4361_; lean_object* v___y_4373_; lean_object* v_i_4374_; lean_object* v___y_4380_; lean_object* v___y_4390_; lean_object* v_i_4391_; lean_object* v___x_4406_; 
v___x_4406_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_4355_, v_e_3381_);
switch(lean_obj_tag(v___x_4406_))
{
case 0:
{
lean_object* v_index_4407_; lean_object* v_size_4408_; lean_object* v___x_4409_; 
v_index_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_index_4407_);
lean_dec_ref_known(v___x_4406_, 3);
v_size_4408_ = lean_ctor_get(v_cache_4355_, 0);
lean_inc(v_size_4408_);
lean_inc(v_a_4335_);
v___x_4409_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_4355_, v_size_4408_, v_index_4407_, v_e_3381_, v_a_4335_);
lean_dec(v_index_4407_);
v___y_4361_ = v___x_4409_;
goto v___jp_4360_;
}
case 1:
{
lean_object* v_index_4410_; lean_object* v_size_4411_; lean_object* v_keyArray_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_index_4410_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_index_4410_);
lean_dec_ref_known(v___x_4406_, 1);
v_size_4411_ = lean_ctor_get(v_cache_4355_, 0);
v_keyArray_4412_ = lean_ctor_get(v_cache_4355_, 1);
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = lean_nat_add(v_size_4411_, v___x_4413_);
v___x_4415_ = lean_array_get_size(v_keyArray_4412_);
v___x_4416_ = lean_nat_dec_lt(v___x_4414_, v___x_4415_);
if (v___x_4416_ == 0)
{
lean_dec(v___x_4414_);
lean_dec(v_index_4410_);
goto v___jp_4396_;
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4417_ = lean_unsigned_to_nat(4u);
v___x_4418_ = lean_nat_mul(v___x_4414_, v___x_4417_);
v___x_4419_ = lean_unsigned_to_nat(3u);
v___x_4420_ = lean_nat_mul(v___x_4415_, v___x_4419_);
v___x_4421_ = lean_nat_dec_le(v___x_4418_, v___x_4420_);
lean_dec(v___x_4420_);
lean_dec(v___x_4418_);
if (v___x_4421_ == 0)
{
lean_dec(v___x_4414_);
lean_dec(v_index_4410_);
goto v___jp_4396_;
}
else
{
lean_object* v___x_4422_; 
lean_inc(v_a_4335_);
v___x_4422_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_4355_, v___x_4414_, v_index_4410_, v_e_3381_, v_a_4335_);
lean_dec(v_index_4410_);
v___y_4361_ = v___x_4422_;
goto v___jp_4360_;
}
}
}
default: 
{
lean_object* v_size_4423_; lean_object* v_keyArray_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v_size_4423_ = lean_ctor_get(v_cache_4355_, 0);
v_keyArray_4424_ = lean_ctor_get(v_cache_4355_, 1);
v___x_4425_ = lean_unsigned_to_nat(1u);
v___x_4426_ = lean_nat_add(v_size_4423_, v___x_4425_);
v___x_4427_ = lean_array_get_size(v_keyArray_4424_);
v___x_4428_ = lean_nat_dec_lt(v___x_4426_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; 
lean_dec(v___x_4426_);
v___x_4429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4355_);
lean_dec_ref(v_cache_4355_);
v___y_4380_ = v___x_4429_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4430_ = lean_unsigned_to_nat(4u);
v___x_4431_ = lean_nat_mul(v___x_4426_, v___x_4430_);
lean_dec(v___x_4426_);
v___x_4432_ = lean_unsigned_to_nat(3u);
v___x_4433_ = lean_nat_mul(v___x_4427_, v___x_4432_);
v___x_4434_ = lean_nat_dec_le(v___x_4431_, v___x_4433_);
lean_dec(v___x_4433_);
lean_dec(v___x_4431_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4355_);
lean_dec_ref(v_cache_4355_);
v___y_4380_ = v___x_4435_;
goto v___jp_4379_;
}
else
{
v___y_4380_ = v_cache_4355_;
goto v___jp_4379_;
}
}
}
}
v___jp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___y_4361_);
v___x_4363_ = v___x_4358_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___y_4361_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_cacheInType_4356_);
v___x_4363_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4365_; 
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 9, v___x_4363_);
v___x_4365_ = v___x_4353_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_share_4341_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_maxFVar_4342_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_proofInstInfo_4343_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_inferType_4344_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v_getLevel_4345_);
lean_ctor_set(v_reuseFailAlloc_4370_, 5, v_congrInfo_4346_);
lean_ctor_set(v_reuseFailAlloc_4370_, 6, v_defEqI_4347_);
lean_ctor_set(v_reuseFailAlloc_4370_, 7, v_extensions_4348_);
lean_ctor_set(v_reuseFailAlloc_4370_, 8, v_issues_4349_);
lean_ctor_set(v_reuseFailAlloc_4370_, 9, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4370_, 10, v_instanceOverrides_4350_);
lean_ctor_set_uint8(v_reuseFailAlloc_4370_, sizeof(void*)*11, v_debug_4351_);
v___x_4365_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4366_ = lean_st_ref_put(v_a_3384_, v___x_4365_);
if (v_isShared_4338_ == 0)
{
v___x_4368_ = v___x_4337_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4335_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
v___jp_4372_:
{
lean_object* v_size_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_size_4375_ = lean_ctor_get(v___y_4373_, 0);
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = lean_nat_add(v_size_4375_, v___x_4376_);
lean_inc(v_a_4335_);
v___x_4378_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4373_, v___x_4377_, v_i_4374_, v_e_3381_, v_a_4335_);
lean_dec(v_i_4374_);
v___y_4361_ = v___x_4378_;
goto v___jp_4360_;
}
v___jp_4379_:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_4380_, v_e_3381_);
switch(lean_obj_tag(v___x_4381_))
{
case 0:
{
lean_object* v_index_4382_; lean_object* v_size_4383_; lean_object* v___x_4384_; 
v_index_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_index_4382_);
lean_dec_ref_known(v___x_4381_, 3);
v_size_4383_ = lean_ctor_get(v___y_4380_, 0);
lean_inc(v_size_4383_);
lean_inc(v_a_4335_);
v___x_4384_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4380_, v_size_4383_, v_index_4382_, v_e_3381_, v_a_4335_);
lean_dec(v_index_4382_);
v___y_4361_ = v___x_4384_;
goto v___jp_4360_;
}
case 1:
{
lean_object* v_index_4385_; 
v_index_4385_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_index_4385_);
lean_dec_ref_known(v___x_4381_, 1);
v___y_4373_ = v___y_4380_;
v_i_4374_ = v_index_4385_;
goto v___jp_4372_;
}
default: 
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4387_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4380_, v___x_4386_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_index_4388_; 
v_index_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_index_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v___y_4373_ = v___y_4380_;
v_i_4374_ = v_index_4388_;
goto v___jp_4372_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_4361_ = v___y_4380_;
goto v___jp_4360_;
}
}
}
}
v___jp_4389_:
{
lean_object* v_size_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_size_4392_ = lean_ctor_get(v___y_4390_, 0);
v___x_4393_ = lean_unsigned_to_nat(1u);
v___x_4394_ = lean_nat_add(v_size_4392_, v___x_4393_);
lean_inc(v_a_4335_);
v___x_4395_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4390_, v___x_4394_, v_i_4391_, v_e_3381_, v_a_4335_);
lean_dec(v_i_4391_);
v___y_4361_ = v___x_4395_;
goto v___jp_4360_;
}
v___jp_4396_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cache_4355_);
lean_dec_ref(v_cache_4355_);
v___x_4398_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_4397_, v_e_3381_);
switch(lean_obj_tag(v___x_4398_))
{
case 0:
{
lean_object* v_index_4399_; lean_object* v_size_4400_; lean_object* v___x_4401_; 
v_index_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_index_4399_);
lean_dec_ref_known(v___x_4398_, 3);
v_size_4400_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_size_4400_);
lean_inc(v_a_4335_);
v___x_4401_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4397_, v_size_4400_, v_index_4399_, v_e_3381_, v_a_4335_);
lean_dec(v_index_4399_);
v___y_4361_ = v___x_4401_;
goto v___jp_4360_;
}
case 1:
{
lean_object* v_index_4402_; 
v_index_4402_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_index_4402_);
lean_dec_ref_known(v___x_4398_, 1);
v___y_4390_ = v___x_4397_;
v_i_4391_ = v_index_4402_;
goto v___jp_4389_;
}
default: 
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_unsigned_to_nat(0u);
v___x_4404_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4397_, v___x_4403_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_index_4405_; 
v_index_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_index_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___y_4390_ = v___x_4397_;
v_i_4391_ = v_index_4405_;
goto v___jp_4389_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_4361_ = v___x_4397_;
goto v___jp_4360_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_4334_;
}
}
}
else
{
lean_object* v___x_4439_; lean_object* v_canon_4440_; lean_object* v_cacheInType_4441_; lean_object* v___x_4442_; 
v___x_4439_ = lean_st_ref_get(v_a_3384_);
v_canon_4440_ = lean_ctor_get(v___x_4439_, 9);
lean_inc_ref(v_canon_4440_);
lean_dec(v___x_4439_);
v_cacheInType_4441_ = lean_ctor_get(v_canon_4440_, 1);
lean_inc_ref(v_cacheInType_4441_);
lean_dec_ref(v_canon_4440_);
v___x_4442_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_4441_, v_e_3381_);
lean_dec_ref(v_cacheInType_4441_);
if (lean_obj_tag(v___x_4442_) == 1)
{
lean_object* v_val_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec_ref_known(v_e_3381_, 3);
v_val_4443_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4442_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_val_4443_);
lean_dec(v___x_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
lean_ctor_set_tag(v___x_4445_, 0);
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_val_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
else
{
lean_object* v___x_4451_; 
lean_dec(v___x_4442_);
lean_inc_ref(v_e_3381_);
v___x_4451_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4555_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4555_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4555_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v_canon_4457_; lean_object* v_share_4458_; lean_object* v_maxFVar_4459_; lean_object* v_proofInstInfo_4460_; lean_object* v_inferType_4461_; lean_object* v_getLevel_4462_; lean_object* v_congrInfo_4463_; lean_object* v_defEqI_4464_; lean_object* v_extensions_4465_; lean_object* v_issues_4466_; lean_object* v_instanceOverrides_4467_; uint8_t v_debug_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4554_; 
v___x_4456_ = lean_st_ref_take(v_a_3384_);
v_canon_4457_ = lean_ctor_get(v___x_4456_, 9);
v_share_4458_ = lean_ctor_get(v___x_4456_, 0);
v_maxFVar_4459_ = lean_ctor_get(v___x_4456_, 1);
v_proofInstInfo_4460_ = lean_ctor_get(v___x_4456_, 2);
v_inferType_4461_ = lean_ctor_get(v___x_4456_, 3);
v_getLevel_4462_ = lean_ctor_get(v___x_4456_, 4);
v_congrInfo_4463_ = lean_ctor_get(v___x_4456_, 5);
v_defEqI_4464_ = lean_ctor_get(v___x_4456_, 6);
v_extensions_4465_ = lean_ctor_get(v___x_4456_, 7);
v_issues_4466_ = lean_ctor_get(v___x_4456_, 8);
v_instanceOverrides_4467_ = lean_ctor_get(v___x_4456_, 10);
v_debug_4468_ = lean_ctor_get_uint8(v___x_4456_, sizeof(void*)*11);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4470_ = v___x_4456_;
v_isShared_4471_ = v_isSharedCheck_4554_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_instanceOverrides_4467_);
lean_inc(v_canon_4457_);
lean_inc(v_issues_4466_);
lean_inc(v_extensions_4465_);
lean_inc(v_defEqI_4464_);
lean_inc(v_congrInfo_4463_);
lean_inc(v_getLevel_4462_);
lean_inc(v_inferType_4461_);
lean_inc(v_proofInstInfo_4460_);
lean_inc(v_maxFVar_4459_);
lean_inc(v_share_4458_);
lean_dec(v___x_4456_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4554_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v_cache_4472_; lean_object* v_cacheInType_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4553_; 
v_cache_4472_ = lean_ctor_get(v_canon_4457_, 0);
v_cacheInType_4473_ = lean_ctor_get(v_canon_4457_, 1);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_canon_4457_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4475_ = v_canon_4457_;
v_isShared_4476_ = v_isSharedCheck_4553_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_cacheInType_4473_);
lean_inc(v_cache_4472_);
lean_dec(v_canon_4457_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4553_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___y_4478_; lean_object* v___y_4490_; lean_object* v_i_4491_; lean_object* v___y_4507_; lean_object* v_i_4508_; lean_object* v___y_4514_; lean_object* v___x_4523_; 
v___x_4523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_4473_, v_e_3381_);
switch(lean_obj_tag(v___x_4523_))
{
case 0:
{
lean_object* v_index_4524_; lean_object* v_size_4525_; lean_object* v___x_4526_; 
v_index_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_index_4524_);
lean_dec_ref_known(v___x_4523_, 3);
v_size_4525_ = lean_ctor_get(v_cacheInType_4473_, 0);
lean_inc(v_size_4525_);
lean_inc(v_a_4452_);
v___x_4526_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4473_, v_size_4525_, v_index_4524_, v_e_3381_, v_a_4452_);
lean_dec(v_index_4524_);
v___y_4478_ = v___x_4526_;
goto v___jp_4477_;
}
case 1:
{
lean_object* v_index_4527_; lean_object* v_size_4528_; lean_object* v_keyArray_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v_index_4527_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_index_4527_);
lean_dec_ref_known(v___x_4523_, 1);
v_size_4528_ = lean_ctor_get(v_cacheInType_4473_, 0);
v_keyArray_4529_ = lean_ctor_get(v_cacheInType_4473_, 1);
v___x_4530_ = lean_unsigned_to_nat(1u);
v___x_4531_ = lean_nat_add(v_size_4528_, v___x_4530_);
v___x_4532_ = lean_array_get_size(v_keyArray_4529_);
v___x_4533_ = lean_nat_dec_lt(v___x_4531_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_dec(v___x_4531_);
lean_dec(v_index_4527_);
goto v___jp_4496_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4534_ = lean_unsigned_to_nat(4u);
v___x_4535_ = lean_nat_mul(v___x_4531_, v___x_4534_);
v___x_4536_ = lean_unsigned_to_nat(3u);
v___x_4537_ = lean_nat_mul(v___x_4532_, v___x_4536_);
v___x_4538_ = lean_nat_dec_le(v___x_4535_, v___x_4537_);
lean_dec(v___x_4537_);
lean_dec(v___x_4535_);
if (v___x_4538_ == 0)
{
lean_dec(v___x_4531_);
lean_dec(v_index_4527_);
goto v___jp_4496_;
}
else
{
lean_object* v___x_4539_; 
lean_inc(v_a_4452_);
v___x_4539_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheInType_4473_, v___x_4531_, v_index_4527_, v_e_3381_, v_a_4452_);
lean_dec(v_index_4527_);
v___y_4478_ = v___x_4539_;
goto v___jp_4477_;
}
}
}
default: 
{
lean_object* v_size_4540_; lean_object* v_keyArray_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v_size_4540_ = lean_ctor_get(v_cacheInType_4473_, 0);
v_keyArray_4541_ = lean_ctor_get(v_cacheInType_4473_, 1);
v___x_4542_ = lean_unsigned_to_nat(1u);
v___x_4543_ = lean_nat_add(v_size_4540_, v___x_4542_);
v___x_4544_ = lean_array_get_size(v_keyArray_4541_);
v___x_4545_ = lean_nat_dec_lt(v___x_4543_, v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
lean_dec(v___x_4543_);
v___x_4546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4473_);
lean_dec_ref(v_cacheInType_4473_);
v___y_4514_ = v___x_4546_;
goto v___jp_4513_;
}
else
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4547_ = lean_unsigned_to_nat(4u);
v___x_4548_ = lean_nat_mul(v___x_4543_, v___x_4547_);
lean_dec(v___x_4543_);
v___x_4549_ = lean_unsigned_to_nat(3u);
v___x_4550_ = lean_nat_mul(v___x_4544_, v___x_4549_);
v___x_4551_ = lean_nat_dec_le(v___x_4548_, v___x_4550_);
lean_dec(v___x_4550_);
lean_dec(v___x_4548_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4473_);
lean_dec_ref(v_cacheInType_4473_);
v___y_4514_ = v___x_4552_;
goto v___jp_4513_;
}
else
{
v___y_4514_ = v_cacheInType_4473_;
goto v___jp_4513_;
}
}
}
}
v___jp_4477_:
{
lean_object* v___x_4480_; 
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 1, v___y_4478_);
v___x_4480_ = v___x_4475_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_cache_4472_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v___y_4478_);
v___x_4480_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4482_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 9, v___x_4480_);
v___x_4482_ = v___x_4470_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_share_4458_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_maxFVar_4459_);
lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_proofInstInfo_4460_);
lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_inferType_4461_);
lean_ctor_set(v_reuseFailAlloc_4487_, 4, v_getLevel_4462_);
lean_ctor_set(v_reuseFailAlloc_4487_, 5, v_congrInfo_4463_);
lean_ctor_set(v_reuseFailAlloc_4487_, 6, v_defEqI_4464_);
lean_ctor_set(v_reuseFailAlloc_4487_, 7, v_extensions_4465_);
lean_ctor_set(v_reuseFailAlloc_4487_, 8, v_issues_4466_);
lean_ctor_set(v_reuseFailAlloc_4487_, 9, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4487_, 10, v_instanceOverrides_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4487_, sizeof(void*)*11, v_debug_4468_);
v___x_4482_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4483_ = lean_st_ref_put(v_a_3384_, v___x_4482_);
if (v_isShared_4455_ == 0)
{
v___x_4485_ = v___x_4454_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4452_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
v___jp_4489_:
{
lean_object* v_size_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_size_4492_ = lean_ctor_get(v___y_4490_, 0);
v___x_4493_ = lean_unsigned_to_nat(1u);
v___x_4494_ = lean_nat_add(v_size_4492_, v___x_4493_);
lean_inc(v_a_4452_);
v___x_4495_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4490_, v___x_4494_, v_i_4491_, v_e_3381_, v_a_4452_);
lean_dec(v_i_4491_);
v___y_4478_ = v___x_4495_;
goto v___jp_4477_;
}
v___jp_4496_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_cacheInType_4473_);
lean_dec_ref(v_cacheInType_4473_);
v___x_4498_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___x_4497_, v_e_3381_);
switch(lean_obj_tag(v___x_4498_))
{
case 0:
{
lean_object* v_index_4499_; lean_object* v_size_4500_; lean_object* v___x_4501_; 
v_index_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_index_4499_);
lean_dec_ref_known(v___x_4498_, 3);
v_size_4500_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_size_4500_);
lean_inc(v_a_4452_);
v___x_4501_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4497_, v_size_4500_, v_index_4499_, v_e_3381_, v_a_4452_);
lean_dec(v_index_4499_);
v___y_4478_ = v___x_4501_;
goto v___jp_4477_;
}
case 1:
{
lean_object* v_index_4502_; 
v_index_4502_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_index_4502_);
lean_dec_ref_known(v___x_4498_, 1);
v___y_4490_ = v___x_4497_;
v_i_4491_ = v_index_4502_;
goto v___jp_4489_;
}
default: 
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4497_, v___x_4503_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_index_4505_; 
v_index_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_index_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v___y_4490_ = v___x_4497_;
v_i_4491_ = v_index_4505_;
goto v___jp_4489_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_4478_ = v___x_4497_;
goto v___jp_4477_;
}
}
}
}
v___jp_4506_:
{
lean_object* v_size_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_size_4509_ = lean_ctor_get(v___y_4507_, 0);
v___x_4510_ = lean_unsigned_to_nat(1u);
v___x_4511_ = lean_nat_add(v_size_4509_, v___x_4510_);
lean_inc(v_a_4452_);
v___x_4512_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4507_, v___x_4511_, v_i_4508_, v_e_3381_, v_a_4452_);
lean_dec(v_i_4508_);
v___y_4478_ = v___x_4512_;
goto v___jp_4477_;
}
v___jp_4513_:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v___y_4514_, v_e_3381_);
switch(lean_obj_tag(v___x_4515_))
{
case 0:
{
lean_object* v_index_4516_; lean_object* v_size_4517_; lean_object* v___x_4518_; 
v_index_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_index_4516_);
lean_dec_ref_known(v___x_4515_, 3);
v_size_4517_ = lean_ctor_get(v___y_4514_, 0);
lean_inc(v_size_4517_);
lean_inc(v_a_4452_);
v___x_4518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4514_, v_size_4517_, v_index_4516_, v_e_3381_, v_a_4452_);
lean_dec(v_index_4516_);
v___y_4478_ = v___x_4518_;
goto v___jp_4477_;
}
case 1:
{
lean_object* v_index_4519_; 
v_index_4519_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_index_4519_);
lean_dec_ref_known(v___x_4515_, 1);
v___y_4507_ = v___y_4514_;
v_i_4508_ = v_index_4519_;
goto v___jp_4506_;
}
default: 
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4514_, v___x_4520_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_index_4522_; 
v_index_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_index_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v___y_4507_ = v___y_4514_;
v_i_4508_ = v_index_4522_;
goto v___jp_4506_;
}
else
{
lean_dec_ref_known(v_e_3381_, 3);
v___y_4478_ = v___y_4514_;
goto v___jp_4477_;
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
lean_dec_ref_known(v_e_3381_, 3);
return v___x_4451_;
}
}
}
}
case 10:
{
lean_object* v_data_4556_; lean_object* v_expr_4557_; lean_object* v___x_4558_; 
v_data_4556_ = lean_ctor_get(v_e_3381_, 0);
v_expr_4557_ = lean_ctor_get(v_e_3381_, 1);
lean_inc_ref(v_expr_4557_);
v___x_4558_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_4557_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4573_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4561_ = v___x_4558_;
v_isShared_4562_ = v_isSharedCheck_4573_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4573_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
size_t v___x_4563_; size_t v___x_4564_; uint8_t v___x_4565_; 
v___x_4563_ = lean_ptr_addr(v_expr_4557_);
v___x_4564_ = lean_ptr_addr(v_a_4559_);
v___x_4565_ = lean_usize_dec_eq(v___x_4563_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
lean_inc(v_data_4556_);
lean_dec_ref_known(v_e_3381_, 2);
v___x_4566_ = l_Lean_Expr_mdata___override(v_data_4556_, v_a_4559_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4566_);
v___x_4568_ = v___x_4561_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
else
{
lean_object* v___x_4571_; 
lean_dec(v_a_4559_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v_e_3381_);
v___x_4571_ = v___x_4561_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_e_3381_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3381_, 2);
return v___x_4558_;
}
}
default: 
{
lean_object* v___x_4574_; 
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v_e_3381_);
return v___x_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_4575_, uint8_t v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
if (v_a_4576_ == 0)
{
lean_object* v___x_4584_; 
lean_inc_ref(v_e_4575_);
v___x_4584_ = l_Lean_Meta_isProp(v_e_4575_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; uint8_t v___x_4586_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4584_, 1);
v___x_4586_ = lean_unbox(v_a_4585_);
lean_dec(v_a_4585_);
if (v___x_4586_ == 0)
{
uint8_t v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = 1;
v___x_4588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4575_, v___x_4587_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4588_;
}
else
{
lean_object* v___x_4589_; 
v___x_4589_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4589_;
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec_ref(v_e_4575_);
v_a_4590_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4584_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4584_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v___x_4598_; 
v___x_4598_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_4599_, lean_object* v_body_4600_, lean_object* v_x_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v___y_71425__boxed_4610_; lean_object* v_res_4611_; 
v___y_71425__boxed_4610_ = lean_unbox(v___y_4602_);
v_res_4611_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_4599_, v_body_4600_, v_x_4601_, v___y_71425__boxed_4610_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_4612_, lean_object* v_e_4613_, uint8_t v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
if (lean_obj_tag(v_e_4613_) == 7)
{
lean_object* v_binderName_4622_; lean_object* v_binderType_4623_; lean_object* v_body_4624_; uint8_t v_binderInfo_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v_binderName_4622_ = lean_ctor_get(v_e_4613_, 0);
lean_inc(v_binderName_4622_);
v_binderType_4623_ = lean_ctor_get(v_e_4613_, 1);
lean_inc_ref(v_binderType_4623_);
v_body_4624_ = lean_ctor_get(v_e_4613_, 2);
lean_inc_ref(v_body_4624_);
v_binderInfo_4625_ = lean_ctor_get_uint8(v_e_4613_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4613_, 3);
v___x_4626_ = lean_expr_instantiate_rev(v_binderType_4623_, v_fvars_4612_);
lean_dec_ref(v_binderType_4623_);
v___x_4627_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_4626_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___f_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref_known(v___x_4627_, 1);
v___f_4629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_4629_, 0, v_fvars_4612_);
lean_closure_set(v___f_4629_, 1, v_body_4624_);
v___x_4630_ = 0;
v___x_4631_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(v_binderName_4622_, v_binderInfo_4625_, v_a_4628_, v___f_4629_, v___x_4630_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
return v___x_4631_;
}
else
{
lean_dec_ref(v_body_4624_);
lean_dec(v_binderName_4622_);
lean_dec_ref(v_fvars_4612_);
return v___x_4627_;
}
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_expr_instantiate_rev(v_e_4613_, v_fvars_4612_);
lean_dec_ref(v_e_4613_);
v___x_4633_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_4632_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; uint8_t v___x_4635_; uint8_t v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref_known(v___x_4633_, 1);
v___x_4635_ = 0;
v___x_4636_ = 1;
v___x_4637_ = 1;
v___x_4638_ = l_Lean_Meta_mkForallFVars(v_fvars_4612_, v_a_4634_, v___x_4635_, v___x_4636_, v___x_4636_, v___x_4637_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec_ref(v_fvars_4612_);
return v___x_4638_;
}
else
{
lean_dec_ref(v_fvars_4612_);
return v___x_4633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_4639_, lean_object* v_body_4640_, lean_object* v_x_4641_, uint8_t v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = lean_array_push(v_fvars_4639_, v_x_4641_);
v___x_4651_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_4650_, v_body_4640_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
uint8_t v_a_boxed_4661_; lean_object* v_res_4662_; 
v_a_boxed_4661_ = lean_unbox(v_a_4653_);
v_res_4662_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_4652_, v_a_boxed_4661_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
uint8_t v_a_boxed_4672_; lean_object* v_res_4673_; 
v_a_boxed_4672_ = lean_unbox(v_a_4664_);
v_res_4673_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_4663_, v_a_boxed_4672_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
uint8_t v_a_boxed_4683_; lean_object* v_res_4684_; 
v_a_boxed_4683_ = lean_unbox(v_a_4675_);
v_res_4684_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_4674_, v_a_boxed_4683_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
uint8_t v_a_boxed_4694_; lean_object* v_res_4695_; 
v_a_boxed_4694_ = lean_unbox(v_a_4686_);
v_res_4695_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_4685_, v_a_boxed_4694_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
uint8_t v_a_boxed_4705_; lean_object* v_res_4706_; 
v_a_boxed_4705_ = lean_unbox(v_a_4697_);
v_res_4706_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_4696_, v_a_boxed_4705_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_4707_, lean_object* v_e_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
uint8_t v_a_boxed_4717_; lean_object* v_res_4718_; 
v_a_boxed_4717_ = lean_unbox(v_a_4709_);
v_res_4718_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_4707_, v_e_4708_, v_a_boxed_4717_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
lean_dec(v_a_4711_);
lean_dec_ref(v_a_4710_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_4719_, lean_object* v_e_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
uint8_t v_a_boxed_4729_; lean_object* v_res_4730_; 
v_a_boxed_4729_ = lean_unbox(v_a_4721_);
v_res_4730_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_4719_, v_e_4720_, v_a_boxed_4729_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_4731_, lean_object* v_report_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
uint8_t v_report_boxed_4741_; uint8_t v_a_boxed_4742_; lean_object* v_res_4743_; 
v_report_boxed_4741_ = lean_unbox(v_report_4732_);
v_a_boxed_4742_ = lean_unbox(v_a_4733_);
v_res_4743_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_4731_, v_report_boxed_4741_, v_a_boxed_4742_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
uint8_t v_a_boxed_4753_; lean_object* v_res_4754_; 
v_a_boxed_4753_ = lean_unbox(v_a_4745_);
v_res_4754_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_4744_, v_a_boxed_4753_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_4755_, lean_object* v_e_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
uint8_t v_a_boxed_4765_; lean_object* v_res_4766_; 
v_a_boxed_4765_ = lean_unbox(v_a_4757_);
v_res_4766_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_4755_, v_e_4756_, v_a_boxed_4765_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_4767_, lean_object* v_00_u03b1_4768_, lean_object* v_c_4769_, lean_object* v_a_4770_, lean_object* v_b_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
uint8_t v_a_boxed_4780_; lean_object* v_res_4781_; 
v_a_boxed_4780_ = lean_unbox(v_a_4772_);
v_res_4781_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_4767_, v_00_u03b1_4768_, v_c_4769_, v_a_4770_, v_b_4771_, v_a_boxed_4780_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_4782_, lean_object* v_00_u03b1_4783_, lean_object* v_c_4784_, lean_object* v_inst_4785_, lean_object* v_a_4786_, lean_object* v_b_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
uint8_t v_a_boxed_4796_; lean_object* v_res_4797_; 
v_a_boxed_4796_ = lean_unbox(v_a_4788_);
v_res_4797_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_4782_, v_00_u03b1_4783_, v_c_4784_, v_inst_4785_, v_a_4786_, v_b_4787_, v_a_boxed_4796_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
lean_dec(v_a_4790_);
lean_dec_ref(v_a_4789_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
uint8_t v_a_boxed_4807_; lean_object* v_res_4808_; 
v_a_boxed_4807_ = lean_unbox(v_a_4799_);
v_res_4808_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_4798_, v_a_boxed_4807_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
uint8_t v_a_boxed_4818_; lean_object* v_res_4819_; 
v_a_boxed_4818_ = lean_unbox(v_a_4810_);
v_res_4819_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_4809_, v_a_boxed_4818_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_4820_, lean_object* v_prop_4821_, lean_object* v_inst_4822_, lean_object* v_e_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
uint8_t v_a_boxed_4832_; lean_object* v_res_4833_; 
v_a_boxed_4832_ = lean_unbox(v_a_4824_);
v_res_4833_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_4820_, v_prop_4821_, v_inst_4822_, v_e_4823_, v_a_boxed_4832_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_upperBound_4834_, lean_object* v___x_4835_, lean_object* v_a_4836_, lean_object* v_b_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
uint8_t v___y_71743__boxed_4846_; lean_object* v_res_4847_; 
v___y_71743__boxed_4846_ = lean_unbox(v___y_4838_);
v_res_4847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_upperBound_4834_, v___x_4835_, v_a_4836_, v_b_4837_, v___y_71743__boxed_4846_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec_ref(v___x_4835_);
lean_dec(v_upperBound_4834_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0___boxed(lean_object* v___x_4848_, lean_object* v_a_4849_, lean_object* v___x_4850_, lean_object* v_snd_4851_, lean_object* v___x_4852_, lean_object* v_fst_4853_, lean_object* v_____r_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
uint8_t v___x_71808__boxed_4863_; uint8_t v___y_71810__boxed_4864_; lean_object* v_res_4865_; 
v___x_71808__boxed_4863_ = lean_unbox(v___x_4852_);
v___y_71810__boxed_4864_ = lean_unbox(v___y_4855_);
v_res_4865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___lam__0(v___x_4848_, v_a_4849_, v___x_4850_, v_snd_4851_, v___x_71808__boxed_4863_, v_fst_4853_, v_____r_4854_, v___y_71810__boxed_4864_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v_a_4849_);
lean_dec_ref(v___x_4848_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
uint8_t v_a_boxed_4875_; lean_object* v_res_4876_; 
v_a_boxed_4875_ = lean_unbox(v_a_4867_);
v_res_4876_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_4866_, v_a_boxed_4875_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
lean_dec(v_a_4873_);
lean_dec_ref(v_a_4872_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_e_4877_, lean_object* v_x_4878_, lean_object* v_x_4879_, lean_object* v_x_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
uint8_t v___y_71949__boxed_4889_; lean_object* v_res_4890_; 
v___y_71949__boxed_4889_ = lean_unbox(v___y_4881_);
v_res_4890_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_e_4877_, v_x_4878_, v_x_4879_, v_x_4880_, v___y_71949__boxed_4889_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_);
lean_dec(v___y_4887_);
lean_dec_ref(v___y_4886_);
lean_dec(v___y_4885_);
lean_dec_ref(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_4891_, lean_object* v_report_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_){
_start:
{
uint8_t v_report_boxed_4901_; uint8_t v_a_boxed_4902_; lean_object* v_res_4903_; 
v_report_boxed_4901_ = lean_unbox(v_report_4892_);
v_a_boxed_4902_ = lean_unbox(v_a_4893_);
v_res_4903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_4891_, v_report_boxed_4901_, v_a_boxed_4902_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
lean_dec(v_a_4899_);
lean_dec_ref(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_4904_, lean_object* v_prop_4905_, lean_object* v_h_4906_, lean_object* v_e_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
uint8_t v_a_boxed_4916_; lean_object* v_res_4917_; 
v_a_boxed_4916_ = lean_unbox(v_a_4908_);
v_res_4917_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_4904_, v_prop_4905_, v_h_4906_, v_e_4907_, v_a_boxed_4916_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_4918_, lean_object* v_prop_4919_, lean_object* v_h_4920_, lean_object* v_e_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_){
_start:
{
uint8_t v_a_boxed_4930_; lean_object* v_res_4931_; 
v_a_boxed_4930_ = lean_unbox(v_a_4922_);
v_res_4931_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_4918_, v_prop_4919_, v_h_4920_, v_e_4921_, v_a_boxed_4930_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
uint8_t v_a_boxed_4941_; lean_object* v_res_4942_; 
v_a_boxed_4941_ = lean_unbox(v_a_4933_);
v_res_4942_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4932_, v_a_boxed_4941_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7(lean_object* v_declName_4943_, uint8_t v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___redArg(v_declName_4943_, v___y_4950_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7___boxed(lean_object* v_declName_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
uint8_t v___y_76353__boxed_4962_; lean_object* v_res_4963_; 
v___y_76353__boxed_4962_ = lean_unbox(v___y_4954_);
v_res_4963_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__7(v_declName_4953_, v___y_76353__boxed_4962_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24(lean_object* v_00_u03b1_4964_, lean_object* v_name_4965_, lean_object* v_type_4966_, lean_object* v_val_4967_, lean_object* v_k_4968_, uint8_t v_nondep_4969_, uint8_t v_kind_4970_, uint8_t v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___redArg(v_name_4965_, v_type_4966_, v_val_4967_, v_k_4968_, v_nondep_4969_, v_kind_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24___boxed(lean_object* v_00_u03b1_4980_, lean_object* v_name_4981_, lean_object* v_type_4982_, lean_object* v_val_4983_, lean_object* v_k_4984_, lean_object* v_nondep_4985_, lean_object* v_kind_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
uint8_t v_nondep_boxed_4995_; uint8_t v_kind_boxed_4996_; uint8_t v___y_76379__boxed_4997_; lean_object* v_res_4998_; 
v_nondep_boxed_4995_ = lean_unbox(v_nondep_4985_);
v_kind_boxed_4996_ = lean_unbox(v_kind_4986_);
v___y_76379__boxed_4997_ = lean_unbox(v___y_4987_);
v_res_4998_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__24(v_00_u03b1_4980_, v_name_4981_, v_type_4982_, v_val_4983_, v_k_4984_, v_nondep_boxed_4995_, v_kind_boxed_4996_, v___y_76379__boxed_4997_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27(lean_object* v_00_u03b1_4999_, lean_object* v_name_5000_, uint8_t v_bi_5001_, lean_object* v_type_5002_, lean_object* v_k_5003_, uint8_t v_kind_5004_, uint8_t v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___redArg(v_name_5000_, v_bi_5001_, v_type_5002_, v_k_5003_, v_kind_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27___boxed(lean_object* v_00_u03b1_5014_, lean_object* v_name_5015_, lean_object* v_bi_5016_, lean_object* v_type_5017_, lean_object* v_k_5018_, lean_object* v_kind_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
uint8_t v_bi_boxed_5028_; uint8_t v_kind_boxed_5029_; uint8_t v___y_76405__boxed_5030_; lean_object* v_res_5031_; 
v_bi_boxed_5028_ = lean_unbox(v_bi_5016_);
v_kind_boxed_5029_ = lean_unbox(v_kind_5019_);
v___y_76405__boxed_5030_ = lean_unbox(v___y_5020_);
v_res_5031_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__27(v_00_u03b1_5014_, v_name_5015_, v_bi_boxed_5028_, v_type_5017_, v_k_5018_, v_kind_boxed_5029_, v___y_76405__boxed_5030_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_5032_, lean_object* v_m_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_5033_, v_a_5034_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_5036_, lean_object* v_m_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_5036_, v_m_5037_, v_a_5038_);
lean_dec_ref(v_a_5038_);
lean_dec_ref(v_m_5037_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_5040_, lean_object* v_m_5041_, lean_object* v_query_5042_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_5041_, v_query_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___boxed(lean_object* v_00_u03b2_5044_, lean_object* v_m_5045_, lean_object* v_query_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(v_00_u03b2_5044_, v_m_5045_, v_query_5046_);
lean_dec_ref(v_query_5046_);
lean_dec_ref(v_m_5045_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3(lean_object* v_00_u03b2_5048_, lean_object* v_m_5049_){
_start:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___redArg(v_m_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3___boxed(lean_object* v_00_u03b2_5051_, lean_object* v_m_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3(v_00_u03b2_5051_, v_m_5052_);
lean_dec_ref(v_m_5052_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_cls_5054_, lean_object* v_msg_5055_, uint8_t v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_cls_5054_, v_msg_5055_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_cls_5065_, lean_object* v_msg_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_){
_start:
{
uint8_t v___y_76437__boxed_5075_; lean_object* v_res_5076_; 
v___y_76437__boxed_5075_ = lean_unbox(v___y_5067_);
v_res_5076_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_cls_5065_, v_msg_5066_, v___y_76437__boxed_5075_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_upperBound_5077_, lean_object* v___x_5078_, lean_object* v___x_5079_, lean_object* v_inst_5080_, lean_object* v_R_5081_, lean_object* v_a_5082_, lean_object* v_b_5083_, lean_object* v_c_5084_, uint8_t v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_upperBound_5077_, v___x_5079_, v_a_5082_, v_b_5083_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_upperBound_5094_, lean_object* v___x_5095_, lean_object* v___x_5096_, lean_object* v_inst_5097_, lean_object* v_R_5098_, lean_object* v_a_5099_, lean_object* v_b_5100_, lean_object* v_c_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
uint8_t v___y_76467__boxed_5110_; lean_object* v_res_5111_; 
v___y_76467__boxed_5110_ = lean_unbox(v___y_5102_);
v_res_5111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_upperBound_5094_, v___x_5095_, v___x_5096_, v_inst_5097_, v_R_5098_, v_a_5099_, v_b_5100_, v_c_5101_, v___y_76467__boxed_5110_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec_ref(v___x_5096_);
lean_dec(v___x_5095_);
lean_dec(v_upperBound_5094_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_5112_, lean_object* v_m_5113_, lean_object* v_query_5114_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_m_5113_, v_query_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_5116_, lean_object* v_m_5117_, lean_object* v_query_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_5116_, v_m_5117_, v_query_5118_);
lean_dec_ref(v_query_5118_);
lean_dec_ref(v_m_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_5120_, lean_object* v_m_5121_, lean_object* v_query_5122_, lean_object* v_x_5123_, lean_object* v_x_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_m_5121_, v_query_5122_, v_x_5123_, v_x_5124_, v_x_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_5128_, lean_object* v_m_5129_, lean_object* v_query_5130_, lean_object* v_x_5131_, lean_object* v_x_5132_, lean_object* v_x_5133_, lean_object* v_x_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_5128_, v_m_5129_, v_query_5130_, v_x_5131_, v_x_5132_, v_x_5133_, v_x_5134_);
lean_dec_ref(v_query_5130_);
lean_dec_ref(v_m_5129_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14(lean_object* v_00_u03b2_5136_, lean_object* v_init_5137_, lean_object* v_b_5138_){
_start:
{
lean_object* v___x_5139_; 
v___x_5139_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___redArg(v_init_5137_, v_b_5138_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14___boxed(lean_object* v_00_u03b2_5140_, lean_object* v_init_5141_, lean_object* v_b_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14(v_00_u03b2_5140_, v_init_5141_, v_b_5142_);
lean_dec_ref(v_b_5142_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28(lean_object* v_00_u03b2_5144_, lean_object* v_b_5145_, lean_object* v_acc_5146_, lean_object* v_i_5147_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___redArg(v_b_5145_, v_acc_5146_, v_i_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28___boxed(lean_object* v_00_u03b2_5149_, lean_object* v_b_5150_, lean_object* v_acc_5151_, lean_object* v_i_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__3_spec__14_spec__28(v_00_u03b2_5149_, v_b_5150_, v_acc_5151_, v_i_5152_);
lean_dec_ref(v_b_5150_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_5154_, lean_object* v_i_5155_, lean_object* v_arg_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_5154_, v_i_5155_, v_arg_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5178_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5178_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5162_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5178_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
uint8_t v___x_5167_; 
v___x_5167_ = lean_unbox(v_a_5163_);
lean_dec(v_a_5163_);
if (v___x_5167_ == 3)
{
uint8_t v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5171_; 
v___x_5168_ = 0;
v___x_5169_ = lean_box(v___x_5168_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 0, v___x_5169_);
v___x_5171_ = v___x_5165_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5169_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
else
{
uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5176_; 
v___x_5173_ = 1;
v___x_5174_ = lean_box(v___x_5173_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 0, v___x_5174_);
v___x_5176_ = v___x_5165_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5174_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
v_a_5179_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5162_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5162_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_5187_, lean_object* v_i_5188_, lean_object* v_arg_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_5187_, v_i_5188_, v_arg_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_i_5188_);
lean_dec_ref(v_pinfos_5187_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_5196_, lean_object* v_opts_5197_, lean_object* v_act_5198_, lean_object* v_decl_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_inc(v___y_5205_);
lean_inc_ref(v___y_5204_);
lean_inc(v___y_5203_);
lean_inc_ref(v___y_5202_);
lean_inc(v___y_5201_);
lean_inc_ref(v___y_5200_);
v___x_5207_ = lean_apply_6(v_act_5198_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
v___x_5208_ = l_Lean_profileitIOUnsafe___redArg(v_category_5196_, v_opts_5197_, v___x_5207_, v_decl_5199_);
return v___x_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_5209_, lean_object* v_opts_5210_, lean_object* v_act_5211_, lean_object* v_decl_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_5209_, v_opts_5210_, v_act_5211_, v_decl_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec_ref(v_opts_5210_);
lean_dec_ref(v_category_5209_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_5221_, lean_object* v_category_5222_, lean_object* v_opts_5223_, lean_object* v_act_5224_, lean_object* v_decl_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_5222_, v_opts_5223_, v_act_5224_, v_decl_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_category_5235_, lean_object* v_opts_5236_, lean_object* v_act_5237_, lean_object* v_decl_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_5234_, v_category_5235_, v_opts_5236_, v_act_5237_, v_decl_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec_ref(v_opts_5236_);
lean_dec_ref(v_category_5235_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_5247_, lean_object* v_e_5248_, uint8_t v___x_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_keyedConfig_5257_; uint8_t v_trackZetaDelta_5258_; lean_object* v_zetaDeltaSet_5259_; lean_object* v_lctx_5260_; lean_object* v_localInstances_5261_; lean_object* v_defEqCtx_x3f_5262_; lean_object* v_synthPendingDepth_5263_; lean_object* v_customCanUnfoldPredicate_x3f_5264_; uint8_t v_univApprox_5265_; uint8_t v_inTypeClassResolution_5266_; uint8_t v_cacheInferType_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v_keyedConfig_5257_ = lean_ctor_get(v___y_5252_, 0);
v_trackZetaDelta_5258_ = lean_ctor_get_uint8(v___y_5252_, sizeof(void*)*7);
v_zetaDeltaSet_5259_ = lean_ctor_get(v___y_5252_, 1);
v_lctx_5260_ = lean_ctor_get(v___y_5252_, 2);
v_localInstances_5261_ = lean_ctor_get(v___y_5252_, 3);
v_defEqCtx_x3f_5262_ = lean_ctor_get(v___y_5252_, 4);
v_synthPendingDepth_5263_ = lean_ctor_get(v___y_5252_, 5);
v_customCanUnfoldPredicate_x3f_5264_ = lean_ctor_get(v___y_5252_, 6);
v_univApprox_5265_ = lean_ctor_get_uint8(v___y_5252_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5266_ = lean_ctor_get_uint8(v___y_5252_, sizeof(void*)*7 + 2);
v_cacheInferType_5267_ = lean_ctor_get_uint8(v___y_5252_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_5257_);
v___x_5268_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5247_, v_keyedConfig_5257_);
lean_inc(v_customCanUnfoldPredicate_x3f_5264_);
lean_inc(v_synthPendingDepth_5263_);
lean_inc(v_defEqCtx_x3f_5262_);
lean_inc_ref(v_localInstances_5261_);
lean_inc_ref(v_lctx_5260_);
lean_inc(v_zetaDeltaSet_5259_);
v___x_5269_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5269_, 0, v___x_5268_);
lean_ctor_set(v___x_5269_, 1, v_zetaDeltaSet_5259_);
lean_ctor_set(v___x_5269_, 2, v_lctx_5260_);
lean_ctor_set(v___x_5269_, 3, v_localInstances_5261_);
lean_ctor_set(v___x_5269_, 4, v_defEqCtx_x3f_5262_);
lean_ctor_set(v___x_5269_, 5, v_synthPendingDepth_5263_);
lean_ctor_set(v___x_5269_, 6, v_customCanUnfoldPredicate_x3f_5264_);
lean_ctor_set_uint8(v___x_5269_, sizeof(void*)*7, v_trackZetaDelta_5258_);
lean_ctor_set_uint8(v___x_5269_, sizeof(void*)*7 + 1, v_univApprox_5265_);
lean_ctor_set_uint8(v___x_5269_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5266_);
lean_ctor_set_uint8(v___x_5269_, sizeof(void*)*7 + 3, v_cacheInferType_5267_);
v___x_5270_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_5248_, v___x_5249_, v___y_5250_, v___y_5251_, v___x_5269_, v___y_5253_, v___y_5254_, v___y_5255_);
lean_dec_ref_known(v___x_5269_, 7);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_5271_, lean_object* v_e_5272_, lean_object* v___x_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
uint8_t v___x_1951__boxed_5281_; uint8_t v___x_1952__boxed_5282_; lean_object* v_res_5283_; 
v___x_1951__boxed_5281_ = lean_unbox(v___x_5271_);
v___x_1952__boxed_5282_ = lean_unbox(v___x_5273_);
v_res_5283_ = l_Lean_Meta_Sym_canon___lam__0(v___x_1951__boxed_5281_, v_e_5272_, v___x_1952__boxed_5282_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
lean_object* v_options_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; uint8_t v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___f_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v_options_5293_ = lean_ctor_get(v_a_5290_, 2);
v___x_5294_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_5295_ = 0;
v___x_5296_ = 2;
v___x_5297_ = lean_box(v___x_5296_);
v___x_5298_ = lean_box(v___x_5295_);
v___f_5299_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5299_, 0, v___x_5297_);
lean_closure_set(v___f_5299_, 1, v_e_5285_);
lean_closure_set(v___f_5299_, 2, v___x_5298_);
v___x_5300_ = lean_box(0);
v___x_5301_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_5294_, v_options_5293_, v___f_5299_, v___x_5300_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_Meta_Sym_canon(v_e_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_a_5306_);
lean_dec_ref(v_a_5305_);
lean_dec(v_a_5304_);
lean_dec_ref(v_a_5303_);
return v_res_5310_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default = _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default();
l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult = _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Canon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Canon(builtin);
}
#ifdef __cplusplus
}
#endif

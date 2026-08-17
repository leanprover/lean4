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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
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
if (v___y_106_ == 0)
{
lean_dec_ref(v___y_105_);
goto v___jp_101_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v___y_105_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
v___jp_109_:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_110_, v___y_113_);
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
v___y_105_ = v___y_111_;
v___y_106_ = v___y_112_;
goto v___jp_104_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_fget_borrowed(v___y_111_, v___x_120_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Int_mkType;
v___x_125_ = lean_array_fset(v___y_111_, v___x_120_, v___x_124_);
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
v___y_105_ = v___y_111_;
v___y_106_ = v___y_112_;
goto v___jp_104_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v___y_111_);
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
v___y_110_ = v_inst_144_;
v___y_111_ = v_args_140_;
v___y_112_ = v_modified_141_;
v___y_113_ = v___y_142_;
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
v___y_110_ = v_inst_144_;
v___y_111_ = v_args_140_;
v___y_112_ = v_modified_141_;
v___y_113_ = v___y_142_;
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
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_264_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_264_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_264_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_264_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v_canon_231_; lean_object* v_share_232_; lean_object* v_maxFVar_233_; lean_object* v_proofInstInfo_234_; lean_object* v_inferType_235_; lean_object* v_getLevel_236_; lean_object* v_congrInfo_237_; lean_object* v_defEqI_238_; lean_object* v_extensions_239_; lean_object* v_issues_240_; lean_object* v_instanceOverrides_241_; uint8_t v_debug_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_263_; 
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
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_263_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_263_;
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
v_isShared_245_ = v_isSharedCheck_263_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_cache_246_; lean_object* v_cacheInType_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_262_; 
v_cache_246_ = lean_ctor_get(v_canon_231_, 0);
v_cacheInType_247_ = lean_ctor_get(v_canon_231_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_canon_231_);
if (v_isSharedCheck_262_ == 0)
{
v___x_249_ = v_canon_231_;
v_isShared_250_ = v_isSharedCheck_262_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cacheInType_247_);
lean_inc(v_cache_246_);
lean_dec(v_canon_231_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_262_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_inc(v_a_226_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_213_, v___x_214_, v_cache_246_, v_e_200_, v_a_226_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_cacheInType_247_);
v___x_253_ = v_reuseFailAlloc_261_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 9, v___x_253_);
v___x_255_ = v___x_244_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_share_232_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_maxFVar_233_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_proofInstInfo_234_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_inferType_235_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_getLevel_236_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_congrInfo_237_);
lean_ctor_set(v_reuseFailAlloc_260_, 6, v_defEqI_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 7, v_extensions_239_);
lean_ctor_set(v_reuseFailAlloc_260_, 8, v_issues_240_);
lean_ctor_set(v_reuseFailAlloc_260_, 9, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_260_, 10, v_instanceOverrides_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_260_, sizeof(void*)*11, v_debug_242_);
v___x_255_ = v_reuseFailAlloc_260_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_st_ref_put(v_a_204_, v___x_255_);
if (v_isShared_229_ == 0)
{
v___x_258_ = v___x_228_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_226_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
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
lean_object* v___x_265_; lean_object* v_canon_266_; lean_object* v_cacheInType_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = lean_st_ref_get(v_a_204_);
v_canon_266_ = lean_ctor_get(v___x_265_, 9);
lean_inc_ref(v_canon_266_);
lean_dec(v___x_265_);
v_cacheInType_267_ = lean_ctor_get(v_canon_266_, 1);
lean_inc_ref(v_cacheInType_267_);
lean_dec_ref(v_canon_266_);
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_200_);
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_268_, v___x_269_, v_cacheInType_267_, v_e_200_);
lean_dec_ref(v_cacheInType_267_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_val_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_k_201_);
lean_dec_ref(v_e_200_);
v_val_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_val_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 0);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_val_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v___x_270_);
v___x_279_ = lean_box(v_a_202_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
v___x_280_ = lean_apply_8(v_k_201_, v___x_279_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_319_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_319_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_319_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_319_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v_canon_286_; lean_object* v_share_287_; lean_object* v_maxFVar_288_; lean_object* v_proofInstInfo_289_; lean_object* v_inferType_290_; lean_object* v_getLevel_291_; lean_object* v_congrInfo_292_; lean_object* v_defEqI_293_; lean_object* v_extensions_294_; lean_object* v_issues_295_; lean_object* v_instanceOverrides_296_; uint8_t v_debug_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_318_; 
v___x_285_ = lean_st_ref_take(v_a_204_);
v_canon_286_ = lean_ctor_get(v___x_285_, 9);
v_share_287_ = lean_ctor_get(v___x_285_, 0);
v_maxFVar_288_ = lean_ctor_get(v___x_285_, 1);
v_proofInstInfo_289_ = lean_ctor_get(v___x_285_, 2);
v_inferType_290_ = lean_ctor_get(v___x_285_, 3);
v_getLevel_291_ = lean_ctor_get(v___x_285_, 4);
v_congrInfo_292_ = lean_ctor_get(v___x_285_, 5);
v_defEqI_293_ = lean_ctor_get(v___x_285_, 6);
v_extensions_294_ = lean_ctor_get(v___x_285_, 7);
v_issues_295_ = lean_ctor_get(v___x_285_, 8);
v_instanceOverrides_296_ = lean_ctor_get(v___x_285_, 10);
v_debug_297_ = lean_ctor_get_uint8(v___x_285_, sizeof(void*)*11);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_318_ == 0)
{
v___x_299_ = v___x_285_;
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_instanceOverrides_296_);
lean_inc(v_canon_286_);
lean_inc(v_issues_295_);
lean_inc(v_extensions_294_);
lean_inc(v_defEqI_293_);
lean_inc(v_congrInfo_292_);
lean_inc(v_getLevel_291_);
lean_inc(v_inferType_290_);
lean_inc(v_proofInstInfo_289_);
lean_inc(v_maxFVar_288_);
lean_inc(v_share_287_);
lean_dec(v___x_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_cache_301_; lean_object* v_cacheInType_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_317_; 
v_cache_301_ = lean_ctor_get(v_canon_286_, 0);
v_cacheInType_302_ = lean_ctor_get(v_canon_286_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_canon_286_);
if (v_isSharedCheck_317_ == 0)
{
v___x_304_ = v_canon_286_;
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_cacheInType_302_);
lean_inc(v_cache_301_);
lean_dec(v_canon_286_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_a_281_);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_268_, v___x_269_, v_cacheInType_302_, v_e_200_, v_a_281_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_cache_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_316_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 9, v___x_308_);
v___x_310_ = v___x_299_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_share_287_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_maxFVar_288_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_proofInstInfo_289_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_inferType_290_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_getLevel_291_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v_congrInfo_292_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_defEqI_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 7, v_extensions_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 8, v_issues_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 9, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 10, v_instanceOverrides_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*11, v_debug_297_);
v___x_310_ = v_reuseFailAlloc_315_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_st_ref_put(v_a_204_, v___x_310_);
if (v_isShared_284_ == 0)
{
v___x_313_ = v___x_283_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_281_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
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
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_320_, lean_object* v_k_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
uint8_t v_a_boxed_330_; lean_object* v_res_331_; 
v_a_boxed_330_ = lean_unbox(v_a_322_);
v_res_331_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_320_, v_k_321_, v_a_boxed_330_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = l_Lean_Expr_cleanupAnnotations(v_e_338_);
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_341_ = l_Lean_Expr_isConstOf(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = l_Lean_Expr_isApp(v___x_339_);
if (v___x_342_ == 0)
{
lean_dec_ref(v___x_339_);
return v___x_342_;
}
else
{
lean_object* v_arg_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_arg_343_ = lean_ctor_get(v___x_339_, 1);
lean_inc_ref(v_arg_343_);
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_339_);
v___x_345_ = l_Lean_Expr_isApp(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v___x_344_);
lean_dec_ref(v_arg_343_);
return v___x_345_;
}
else
{
lean_object* v_arg_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_arg_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc_ref(v_arg_346_);
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_344_);
v___x_348_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v___x_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_349_, v___x_350_);
lean_dec_ref(v___x_349_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = l_Lean_Expr_isBoolTrue(v_arg_346_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_arg_343_);
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Expr_isBoolTrue(v_arg_343_);
return v___x_353_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_339_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_Expr_cleanupAnnotations(v_e_360_);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_isApp(v___x_361_);
if (v___x_364_ == 0)
{
lean_dec_ref(v___x_361_);
return v___x_364_;
}
else
{
lean_object* v_arg_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_arg_365_ = lean_ctor_get(v___x_361_, 1);
lean_inc_ref(v_arg_365_);
v___x_366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_361_);
v___x_367_ = l_Lean_Expr_isApp(v___x_366_);
if (v___x_367_ == 0)
{
lean_dec_ref(v___x_366_);
lean_dec_ref(v_arg_365_);
return v___x_367_;
}
else
{
lean_object* v_arg_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_arg_368_ = lean_ctor_get(v___x_366_, 1);
lean_inc_ref(v_arg_368_);
v___x_369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_366_);
v___x_370_ = l_Lean_Expr_isApp(v___x_369_);
if (v___x_370_ == 0)
{
lean_dec_ref(v___x_369_);
lean_dec_ref(v_arg_368_);
lean_dec_ref(v_arg_365_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_369_);
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_373_ = l_Lean_Expr_isConstOf(v___x_371_, v___x_372_);
lean_dec_ref(v___x_371_);
if (v___x_373_ == 0)
{
lean_dec_ref(v_arg_368_);
lean_dec_ref(v_arg_365_);
return v___x_373_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = l_Lean_Expr_isBoolFalse(v_arg_368_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_arg_365_);
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_Expr_isBoolTrue(v_arg_365_);
return v___x_375_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_361_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_379_){
_start:
{
switch(v_x_379_)
{
case 0:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(0u);
return v___x_380_;
}
case 1:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(1u);
return v___x_381_;
}
case 2:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(2u);
return v___x_382_;
}
default: 
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(3u);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_384_){
_start:
{
uint8_t v_x_boxed_385_; lean_object* v_res_386_; 
v_x_boxed_385_ = lean_unbox(v_x_384_);
v_res_386_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_387_){
_start:
{
lean_inc(v_k_387_);
return v_k_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_388_);
lean_dec(v_k_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_390_, lean_object* v_ctorIdx_391_, uint8_t v_t_392_, lean_object* v_h_393_, lean_object* v_k_394_){
_start:
{
lean_inc(v_k_394_);
return v_k_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_395_, lean_object* v_ctorIdx_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_k_399_){
_start:
{
uint8_t v_t_boxed_400_; lean_object* v_res_401_; 
v_t_boxed_400_ = lean_unbox(v_t_397_);
v_res_401_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_395_, v_ctorIdx_396_, v_t_boxed_400_, v_h_398_, v_k_399_);
lean_dec(v_k_399_);
lean_dec(v_ctorIdx_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_402_){
_start:
{
lean_inc(v_canonType_402_);
return v_canonType_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_403_);
lean_dec(v_canonType_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_405_, uint8_t v_t_406_, lean_object* v_h_407_, lean_object* v_canonType_408_){
_start:
{
lean_inc(v_canonType_408_);
return v_canonType_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_canonType_412_){
_start:
{
uint8_t v_t_boxed_413_; lean_object* v_res_414_; 
v_t_boxed_413_ = lean_unbox(v_t_410_);
v_res_414_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_409_, v_t_boxed_413_, v_h_411_, v_canonType_412_);
lean_dec(v_canonType_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_415_){
_start:
{
lean_inc(v_canonInst_415_);
return v_canonInst_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_416_);
lean_dec(v_canonInst_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_418_, uint8_t v_t_419_, lean_object* v_h_420_, lean_object* v_canonInst_421_){
_start:
{
lean_inc(v_canonInst_421_);
return v_canonInst_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_canonInst_425_){
_start:
{
uint8_t v_t_boxed_426_; lean_object* v_res_427_; 
v_t_boxed_426_ = lean_unbox(v_t_423_);
v_res_427_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_422_, v_t_boxed_426_, v_h_424_, v_canonInst_425_);
lean_dec(v_canonInst_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_428_){
_start:
{
lean_inc(v_canonImplicit_428_);
return v_canonImplicit_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_429_);
lean_dec(v_canonImplicit_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_431_, uint8_t v_t_432_, lean_object* v_h_433_, lean_object* v_canonImplicit_434_){
_start:
{
lean_inc(v_canonImplicit_434_);
return v_canonImplicit_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_canonImplicit_438_){
_start:
{
uint8_t v_t_boxed_439_; lean_object* v_res_440_; 
v_t_boxed_439_ = lean_unbox(v_t_436_);
v_res_440_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_435_, v_t_boxed_439_, v_h_437_, v_canonImplicit_438_);
lean_dec(v_canonImplicit_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_441_){
_start:
{
lean_inc(v_visit_441_);
return v_visit_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_442_);
lean_dec(v_visit_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_444_, uint8_t v_t_445_, lean_object* v_h_446_, lean_object* v_visit_447_){
_start:
{
lean_inc(v_visit_447_);
return v_visit_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_visit_451_){
_start:
{
uint8_t v_t_boxed_452_; lean_object* v_res_453_; 
v_t_boxed_452_ = lean_unbox(v_t_449_);
v_res_453_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_448_, v_t_boxed_452_, v_h_450_, v_visit_451_);
lean_dec(v_visit_451_);
return v_res_453_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_468_, lean_object* v_x_469_){
_start:
{
switch(v_r_468_)
{
case 0:
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_470_;
}
case 1:
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_471_;
}
case 2:
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_472_;
}
default: 
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_r_boxed_476_; lean_object* v_res_477_; 
v_r_boxed_476_ = lean_unbox(v_r_474_);
v_res_477_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_476_, v_x_475_);
lean_dec(v_x_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_480_, lean_object* v_i_481_, lean_object* v_arg_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_get_size(v_pinfos_480_);
v___x_539_ = lean_nat_dec_lt(v_i_481_, v___x_538_);
if (v___x_539_ == 0)
{
v___y_489_ = v_a_483_;
v___y_490_ = v_a_484_;
v___y_491_ = v_a_485_;
v___y_492_ = v_a_486_;
goto v___jp_488_;
}
else
{
lean_object* v_pinfo_540_; uint8_t v_isInstance_541_; 
v_pinfo_540_ = lean_array_fget_borrowed(v_pinfos_480_, v_i_481_);
v_isInstance_541_ = lean_ctor_get_uint8(v_pinfo_540_, sizeof(void*)*1 + 4);
if (v_isInstance_541_ == 0)
{
uint8_t v_isProp_542_; 
v_isProp_542_ = lean_ctor_get_uint8(v_pinfo_540_, sizeof(void*)*1 + 2);
if (v_isProp_542_ == 0)
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_540_);
if (v___x_543_ == 0)
{
v___y_489_ = v_a_483_;
v___y_490_ = v_a_484_;
v___y_491_ = v_a_485_;
v___y_492_ = v_a_486_;
goto v___jp_488_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Meta_isTypeFormer(v_arg_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_560_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; 
v___x_549_ = lean_unbox(v_a_545_);
lean_dec(v_a_545_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = 2;
v___x_551_ = lean_box(v___x_550_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_551_);
v___x_553_ = v___x_547_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = 0;
v___x_556_ = lean_box(v___x_555_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_556_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_544_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_544_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
else
{
uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_arg_482_);
v___x_569_ = 3;
v___x_570_ = lean_box(v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
else
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_arg_482_);
v___x_572_ = 1;
v___x_573_ = lean_box(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
v___jp_488_:
{
lean_object* v___x_493_; 
lean_inc_ref(v_arg_482_);
v___x_493_ = l_Lean_Meta_isProp(v_arg_482_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_529_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_529_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_529_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_529_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; 
v___x_498_ = lean_unbox(v_a_494_);
lean_dec(v_a_494_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_del_object(v___x_496_);
v___x_499_ = l_Lean_Meta_isTypeFormer(v_arg_482_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_515_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_515_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___x_504_; 
v___x_504_ = lean_unbox(v_a_500_);
lean_dec(v_a_500_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = 3;
v___x_506_ = lean_box(v___x_505_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = 0;
v___x_511_ = lean_box(v___x_510_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_511_);
v___x_513_ = v___x_502_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_499_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_499_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec_ref(v_arg_482_);
v___x_524_ = 3;
v___x_525_ = lean_box(v___x_524_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_525_);
v___x_527_ = v___x_496_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v_arg_482_);
v_a_530_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_493_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_493_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_575_, lean_object* v_i_576_, lean_object* v_arg_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_575_, v_i_576_, v_arg_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_i_576_);
lean_dec_ref(v_pinfos_575_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_584_, lean_object* v_offset_585_){
_start:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_eq(v_offset_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l_Lean_mkNatLit(v_offset_585_);
v___x_589_ = l_Lean_mkNatAdd(v_e_584_, v___x_588_);
return v___x_589_;
}
else
{
lean_dec(v_offset_585_);
return v_e_584_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; lean_object* v_dummy_591_; 
v___x_590_ = lean_box(0);
v_dummy_591_ = l_Lean_Expr_sort___override(v___x_590_);
return v_dummy_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_592_, lean_object* v_e_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
uint8_t v_fromClass_599_; 
v_fromClass_599_ = lean_ctor_get_uint8(v_info_592_, sizeof(void*)*3);
if (v_fromClass_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_593_, v_fromClass_599_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_636_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_636_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_636_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_636_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
if (lean_obj_tag(v_a_601_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_del_object(v___x_603_);
v_val_605_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_a_601_, 1);
v___x_606_ = l_Lean_Expr_getAppFn(v_val_605_);
v___x_607_ = l_Lean_Meta_reduceProj_x3f(v___x_606_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
if (lean_obj_tag(v_a_608_) == 0)
{
lean_dec(v_val_605_);
return v___x_607_;
}
else
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_631_);
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_630_;
goto v_resetjp_609_;
}
else
{
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_630_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_val_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_629_; 
v_val_612_ = lean_ctor_get(v_a_608_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_629_ == 0)
{
v___x_614_ = v_a_608_;
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_val_612_);
lean_dec(v_a_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_dummy_616_; lean_object* v_nargs_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v_dummy_616_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_617_ = l_Lean_Expr_getAppNumArgs(v_val_605_);
lean_inc(v_nargs_617_);
v___x_618_ = lean_mk_array(v_nargs_617_, v_dummy_616_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_sub(v_nargs_617_, v___x_619_);
lean_dec(v_nargs_617_);
v___x_621_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_605_, v___x_618_, v___x_620_);
v___x_622_ = l_Lean_mkAppN(v_val_612_, v___x_621_);
lean_dec_ref(v___x_621_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_622_);
v___x_624_ = v___x_614_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_624_);
v___x_626_ = v___x_610_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
else
{
lean_dec(v_val_605_);
return v___x_607_;
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_634_; 
lean_dec(v_a_601_);
v___x_632_ = lean_box(0);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_632_);
v___x_634_ = v___x_603_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
return v___x_600_;
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_e_593_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_639_, lean_object* v_e_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_639_, v_e_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec_ref(v_info_639_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_647_, lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_647_, v_e_648_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_657_, lean_object* v_e_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_657_, v_e_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec_ref(v_info_657_);
return v_res_666_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_669_ = l_Lean_Expr_isConstOf(v_e_667_, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_670_);
lean_dec_ref(v_e_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = l_Lean_Expr_cleanupAnnotations(v_e_706_);
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_709_ = l_Lean_Expr_isConstOf(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_Expr_isApp(v___x_707_);
if (v___x_710_ == 0)
{
lean_dec_ref(v___x_707_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_707_);
v___x_712_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_713_ = l_Lean_Expr_isConstOf(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_Expr_isApp(v___x_711_);
if (v___x_714_ == 0)
{
lean_dec_ref(v___x_711_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
v___x_716_ = l_Lean_Expr_isApp(v___x_715_);
if (v___x_716_ == 0)
{
lean_dec_ref(v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_715_);
v___x_718_ = l_Lean_Expr_isApp(v___x_717_);
if (v___x_718_ == 0)
{
lean_dec_ref(v___x_717_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = l_Lean_Expr_appFnCleanup___redArg(v___x_717_);
v___x_720_ = l_Lean_Expr_isApp(v___x_719_);
if (v___x_720_ == 0)
{
lean_dec_ref(v___x_719_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_719_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v___x_721_);
return v___x_722_;
}
else
{
lean_object* v_arg_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_arg_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc_ref(v_arg_723_);
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_726_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_728_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_730_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_732_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_734_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_733_);
lean_dec_ref(v___x_724_);
if (v___x_734_ == 0)
{
lean_dec_ref(v_arg_723_);
return v___x_734_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_723_);
lean_dec_ref(v_arg_723_);
return v___x_735_;
}
}
else
{
uint8_t v___x_736_; 
lean_dec_ref(v___x_724_);
v___x_736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_723_);
lean_dec_ref(v_arg_723_);
return v___x_736_;
}
}
else
{
uint8_t v___x_737_; 
lean_dec_ref(v___x_724_);
v___x_737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_723_);
lean_dec_ref(v_arg_723_);
return v___x_737_;
}
}
else
{
uint8_t v___x_738_; 
lean_dec_ref(v___x_724_);
v___x_738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_723_);
lean_dec_ref(v_arg_723_);
return v___x_738_;
}
}
else
{
uint8_t v___x_739_; 
lean_dec_ref(v___x_724_);
v___x_739_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_723_);
lean_dec_ref(v_arg_723_);
return v___x_739_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_711_);
return v___x_713_;
}
}
}
else
{
lean_dec_ref(v___x_707_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_749_, lean_object* v_inst_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; 
lean_inc_ref(v_inst_750_);
lean_inc_ref(v_e_749_);
v___x_758_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_749_, v_inst_750_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_809_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_809_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_809_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_809_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_del_object(v___x_761_);
v___x_764_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_751_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_797_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_797_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_797_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_797_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
uint8_t v_verbose_769_; 
v_verbose_769_ = lean_ctor_get_uint8(v_a_765_, 0);
lean_dec(v_a_765_);
if (v_verbose_769_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_inst_750_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_e_749_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_e_749_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_767_);
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_749_);
v___x_774_ = l_Lean_indentExpr(v_e_749_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_indentExpr(v_inst_750_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_Meta_Sym_reportIssue(v___x_779_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_780_, 0);
lean_dec(v_unused_788_);
v___x_782_ = v___x_780_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_dec(v___x_780_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_e_749_);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_e_749_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v_e_749_);
v_a_789_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_780_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_780_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_inst_750_);
lean_dec_ref(v_e_749_);
v_a_798_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_764_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_764_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v___x_807_; 
lean_dec_ref(v_e_749_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_inst_750_);
v___x_807_ = v___x_761_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_inst_750_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_inst_750_);
lean_dec_ref(v_e_749_);
v_a_810_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_758_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_758_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_818_, lean_object* v_inst_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_818_, v_inst_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_env_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_832_, v_declName_828_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_835_, v___y_836_);
lean_dec(v___y_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_839_, uint8_t v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_839_, v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___y_4074__boxed_858_; lean_object* v_res_859_; 
v___y_4074__boxed_858_ = lean_unbox(v___y_850_);
v_res_859_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_849_, v___y_4074__boxed_858_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_860_, uint8_t v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
uint8_t v___x_869_; 
lean_inc_ref(v_e_860_);
v___x_869_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_860_);
if (v___x_869_ == 0)
{
lean_object* v_f_870_; 
v_f_870_ = l_Lean_Expr_getAppFn(v_e_860_);
if (lean_obj_tag(v_f_870_) == 4)
{
lean_object* v_declName_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_902_; 
v_declName_871_ = lean_ctor_get(v_f_870_, 0);
lean_inc(v_declName_871_);
lean_dec_ref_known(v_f_870_, 2);
v___x_872_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_871_, v_a_867_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_902_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_902_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_902_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
if (lean_obj_tag(v_a_873_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_878_; 
lean_del_object(v___x_875_);
v_val_877_ = lean_ctor_get(v_a_873_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v_a_873_, 1);
lean_inc_ref(v_e_860_);
v___x_878_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_877_, v_e_860_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_val_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_890_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_e_860_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_e_860_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v_val_886_; lean_object* v___x_888_; 
lean_dec_ref(v_e_860_);
v_val_886_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v_a_879_, 1);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_val_886_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_val_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_e_860_);
v_a_891_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_878_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_878_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v___x_900_; 
lean_dec(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_e_860_);
v___x_900_ = v___x_875_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_e_860_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v_f_870_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v_e_860_);
return v___x_903_;
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc_ref(v_e_860_);
v___x_904_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_904_, 0, v_e_860_);
v___x_905_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_904_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_939_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_939_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_939_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_939_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec_ref(v_e_860_);
v_val_910_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v_a_906_, 1);
v___x_911_ = l_Lean_mkNatLit(v_val_910_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v___x_915_; 
lean_del_object(v___x_908_);
lean_dec(v_a_906_);
lean_inc_ref(v_e_860_);
v___x_915_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_860_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_930_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_930_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_a_916_) == 1)
{
lean_object* v_val_920_; lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec_ref(v_e_860_);
v_val_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v_a_916_, 1);
v_fst_921_ = lean_ctor_get(v_val_920_, 0);
lean_inc(v_fst_921_);
v_snd_922_ = lean_ctor_get(v_val_920_, 1);
lean_inc(v_snd_922_);
lean_dec(v_val_920_);
v___x_923_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_921_, v_snd_922_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_923_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_928_; 
lean_dec(v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_e_860_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_e_860_);
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
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_e_860_);
v_a_931_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_915_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_915_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_e_860_);
v_a_940_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_905_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_905_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_a_boxed_957_; lean_object* v_res_958_; 
v_a_boxed_957_ = lean_unbox(v_a_949_);
v_res_958_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_948_, v_a_boxed_957_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_962_, lean_object* v_type_963_, uint8_t v_report_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc_ref(v_type_963_);
v___x_972_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_963_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1024_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1024_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1024_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_978_; 
lean_del_object(v___x_975_);
lean_dec_ref(v_type_963_);
v_val_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_a_973_, 1);
v___x_978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_962_, v_val_977_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_978_;
}
else
{
lean_dec(v_a_973_);
if (v_report_964_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_type_963_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_e_962_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_e_962_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v___x_982_; 
lean_del_object(v___x_975_);
v___x_982_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_965_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1015_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1015_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1015_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
uint8_t v_verbose_987_; 
v_verbose_987_ = lean_ctor_get_uint8(v_a_983_, 0);
lean_dec(v_a_983_);
if (v_verbose_987_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_type_963_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v_e_962_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_e_962_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_985_);
v___x_991_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_962_);
v___x_992_ = l_Lean_indentExpr(v_e_962_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_indentExpr(v_type_963_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_Meta_Sym_reportIssue(v___x_997_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_998_, 0);
lean_dec(v_unused_1006_);
v___x_1000_ = v___x_998_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_dec(v___x_998_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_e_962_);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_e_962_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_e_962_);
v_a_1007_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_998_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_998_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v_type_963_);
lean_dec_ref(v_e_962_);
v_a_1016_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_982_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_982_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref(v_type_963_);
lean_dec_ref(v_e_962_);
v_a_1025_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_972_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_972_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1033_, lean_object* v_type_1034_, lean_object* v_report_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_report_boxed_1043_; lean_object* v_res_1044_; 
v_report_boxed_1043_ = lean_unbox(v_report_1035_);
v_res_1044_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1033_, v_type_1034_, v_report_boxed_1043_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1045_, lean_object* v_type_1046_, uint8_t v_report_1047_, uint8_t v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1045_, v_type_1046_, v_report_1047_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1057_, lean_object* v_type_1058_, lean_object* v_report_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
uint8_t v_report_boxed_1068_; uint8_t v_a_boxed_1069_; lean_object* v_res_1070_; 
v_report_boxed_1068_ = lean_unbox(v_report_1059_);
v_a_boxed_1069_ = lean_unbox(v_a_1060_);
v_res_1070_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1057_, v_type_1058_, v_report_boxed_1068_, v_a_boxed_1069_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = 0;
return v___x_1073_;
}
else
{
lean_object* v_key_1074_; lean_object* v_tail_1075_; uint8_t v___x_1076_; 
v_key_1074_ = lean_ctor_get(v_x_1072_, 0);
v_tail_1075_ = lean_ctor_get(v_x_1072_, 2);
v___x_1076_ = lean_expr_eqv(v_key_1074_, v_a_1071_);
if (v___x_1076_ == 0)
{
v_x_1072_ = v_tail_1075_;
goto _start;
}
else
{
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1078_, lean_object* v_x_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1078_, v_x_1079_);
lean_dec(v_x_1079_);
lean_dec_ref(v_a_1078_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
return v_x_1082_;
}
else
{
lean_object* v_key_1084_; lean_object* v_value_1085_; lean_object* v_tail_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1109_; 
v_key_1084_ = lean_ctor_get(v_x_1083_, 0);
v_value_1085_ = lean_ctor_get(v_x_1083_, 1);
v_tail_1086_ = lean_ctor_get(v_x_1083_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1083_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1088_ = v_x_1083_;
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_tail_1086_);
lean_inc(v_value_1085_);
lean_inc(v_key_1084_);
lean_dec(v_x_1083_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v_fold_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1090_ = lean_array_get_size(v_x_1082_);
v___x_1091_ = l_Lean_Expr_hash(v_key_1084_);
v___x_1092_ = 32ULL;
v___x_1093_ = lean_uint64_shift_right(v___x_1091_, v___x_1092_);
v_fold_1094_ = lean_uint64_xor(v___x_1091_, v___x_1093_);
v___x_1095_ = 16ULL;
v___x_1096_ = lean_uint64_shift_right(v_fold_1094_, v___x_1095_);
v___x_1097_ = lean_uint64_xor(v_fold_1094_, v___x_1096_);
v___x_1098_ = lean_uint64_to_usize(v___x_1097_);
v___x_1099_ = lean_usize_of_nat(v___x_1090_);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_sub(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_usize_land(v___x_1098_, v___x_1101_);
v___x_1103_ = lean_array_uget_borrowed(v_x_1082_, v___x_1102_);
lean_inc(v___x_1103_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 2, v___x_1103_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_key_1084_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_value_1085_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_array_uset(v_x_1082_, v___x_1102_, v___x_1105_);
v_x_1082_ = v___x_1106_;
v_x_1083_ = v_tail_1086_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object* v_i_1110_, lean_object* v_source_1111_, lean_object* v_target_1112_){
_start:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_array_get_size(v_source_1111_);
v___x_1114_ = lean_nat_dec_lt(v_i_1110_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_source_1111_);
lean_dec(v_i_1110_);
return v_target_1112_;
}
else
{
lean_object* v_es_1115_; lean_object* v___x_1116_; lean_object* v_source_1117_; lean_object* v_target_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_es_1115_ = lean_array_fget(v_source_1111_, v_i_1110_);
v___x_1116_ = lean_box(0);
v_source_1117_ = lean_array_fset(v_source_1111_, v_i_1110_, v___x_1116_);
v_target_1118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_1112_, v_es_1115_);
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_add(v_i_1110_, v___x_1119_);
lean_dec(v_i_1110_);
v_i_1110_ = v___x_1120_;
v_source_1111_ = v_source_1117_;
v_target_1112_ = v_target_1118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_nbuckets_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1123_ = lean_array_get_size(v_data_1122_);
v___x_1124_ = lean_unsigned_to_nat(2u);
v_nbuckets_1125_ = lean_nat_mul(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_mk_array(v_nbuckets_1125_, v___x_1127_);
v___x_1129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_1126_, v_data_1122_, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1130_, lean_object* v_b_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_dec(v_b_1131_);
lean_dec_ref(v_a_1130_);
return v_x_1132_;
}
else
{
lean_object* v_key_1133_; lean_object* v_value_1134_; lean_object* v_tail_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1147_; 
v_key_1133_ = lean_ctor_get(v_x_1132_, 0);
v_value_1134_ = lean_ctor_get(v_x_1132_, 1);
v_tail_1135_ = lean_ctor_get(v_x_1132_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1137_ = v_x_1132_;
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_tail_1135_);
lean_inc(v_value_1134_);
lean_inc(v_key_1133_);
lean_dec(v_x_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_expr_eqv(v_key_1133_, v_a_1130_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1130_, v_b_1131_, v_tail_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 2, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_key_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_value_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1145_; 
lean_dec(v_value_1134_);
lean_dec(v_key_1133_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v_b_1131_);
lean_ctor_set(v___x_1137_, 0, v_a_1130_);
v___x_1145_ = v___x_1137_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1130_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_b_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_tail_1135_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_){
_start:
{
lean_object* v_size_1151_; lean_object* v_buckets_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1195_; 
v_size_1151_ = lean_ctor_get(v_m_1148_, 0);
v_buckets_1152_ = lean_ctor_get(v_m_1148_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_m_1148_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1154_ = v_m_1148_;
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_buckets_1152_);
lean_inc(v_size_1151_);
lean_dec(v_m_1148_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v_fold_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; lean_object* v_bkt_1169_; uint8_t v___x_1170_; 
v___x_1156_ = lean_array_get_size(v_buckets_1152_);
v___x_1157_ = l_Lean_Expr_hash(v_a_1149_);
v___x_1158_ = 32ULL;
v___x_1159_ = lean_uint64_shift_right(v___x_1157_, v___x_1158_);
v_fold_1160_ = lean_uint64_xor(v___x_1157_, v___x_1159_);
v___x_1161_ = 16ULL;
v___x_1162_ = lean_uint64_shift_right(v_fold_1160_, v___x_1161_);
v___x_1163_ = lean_uint64_xor(v_fold_1160_, v___x_1162_);
v___x_1164_ = lean_uint64_to_usize(v___x_1163_);
v___x_1165_ = lean_usize_of_nat(v___x_1156_);
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_sub(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_usize_land(v___x_1164_, v___x_1167_);
v_bkt_1169_ = lean_array_uget_borrowed(v_buckets_1152_, v___x_1168_);
v___x_1170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1149_, v_bkt_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v_size_x27_1172_; lean_object* v___x_1173_; lean_object* v_buckets_x27_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v_size_x27_1172_ = lean_nat_add(v_size_1151_, v___x_1171_);
lean_dec(v_size_1151_);
lean_inc(v_bkt_1169_);
v___x_1173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1173_, 0, v_a_1149_);
lean_ctor_set(v___x_1173_, 1, v_b_1150_);
lean_ctor_set(v___x_1173_, 2, v_bkt_1169_);
v_buckets_x27_1174_ = lean_array_uset(v_buckets_1152_, v___x_1168_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(4u);
v___x_1176_ = lean_nat_mul(v_size_x27_1172_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(3u);
v___x_1178_ = lean_nat_div(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_array_get_size(v_buckets_x27_1174_);
v___x_1180_ = lean_nat_dec_le(v___x_1178_, v___x_1179_);
lean_dec(v___x_1178_);
if (v___x_1180_ == 0)
{
lean_object* v_val_1181_; lean_object* v___x_1183_; 
v_val_1181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1174_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_val_1181_);
lean_ctor_set(v___x_1154_, 0, v_size_x27_1172_);
v___x_1183_ = v___x_1154_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_size_x27_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_val_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1186_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_buckets_x27_1174_);
lean_ctor_set(v___x_1154_, 0, v_size_x27_1172_);
v___x_1186_ = v___x_1154_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_size_x27_1172_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_buckets_x27_1174_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v_buckets_x27_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v_bkt_1169_);
v___x_1188_ = lean_box(0);
v_buckets_x27_1189_ = lean_array_uset(v_buckets_1152_, v___x_1168_, v___x_1188_);
v___x_1190_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1149_, v_b_1150_, v_bkt_1169_);
v___x_1191_ = lean_array_uset(v_buckets_x27_1189_, v___x_1168_, v___x_1190_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1191_);
v___x_1193_ = v___x_1154_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_size_1151_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object* v_k_1196_, uint8_t v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_box(v___y_1197_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
v___x_1207_ = lean_apply_9(v_k_1196_, v_b_1200_, v___x_1206_, v___y_1198_, v___y_1199_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, lean_box(0));
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object* v_k_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v___y_67971__boxed_1218_; lean_object* v_res_1219_; 
v___y_67971__boxed_1218_ = lean_unbox(v___y_1209_);
v_res_1219_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1208_, v___y_67971__boxed_1218_, v___y_1210_, v___y_1211_, v_b_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object* v_name_1220_, uint8_t v_bi_1221_, lean_object* v_type_1222_, lean_object* v_k_1223_, uint8_t v_kind_1224_, uint8_t v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_box(v___y_1225_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
v___f_1234_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1234_, 0, v_k_1223_);
lean_closure_set(v___f_1234_, 1, v___x_1233_);
lean_closure_set(v___f_1234_, 2, v___y_1226_);
lean_closure_set(v___f_1234_, 3, v___y_1227_);
v___x_1235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1220_, v_bi_1221_, v_type_1222_, v___f_1234_, v_kind_1224_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1235_) == 0)
{
return v___x_1235_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object* v_name_1244_, lean_object* v_bi_1245_, lean_object* v_type_1246_, lean_object* v_k_1247_, lean_object* v_kind_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_bi_boxed_1257_; uint8_t v_kind_boxed_1258_; uint8_t v___y_67999__boxed_1259_; lean_object* v_res_1260_; 
v_bi_boxed_1257_ = lean_unbox(v_bi_1245_);
v_kind_boxed_1258_ = lean_unbox(v_kind_1248_);
v___y_67999__boxed_1259_ = lean_unbox(v___y_1249_);
v_res_1260_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1244_, v_bi_boxed_1257_, v_type_1246_, v_k_1247_, v_kind_boxed_1258_, v___y_67999__boxed_1259_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_env_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1264_ = lean_st_ref_get(v___y_1262_);
v_env_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc_ref(v_env_1265_);
lean_dec(v___x_1264_);
v___x_1266_ = l_Lean_Meta_isMatcherCore(v_env_1265_, v_declName_1261_);
v___x_1267_ = lean_box(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1269_, v___y_1270_);
lean_dec(v___y_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object* v_msgData_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_env_1280_; lean_object* v___x_1281_; lean_object* v_mctx_1282_; lean_object* v_lctx_1283_; lean_object* v_options_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1279_ = lean_st_ref_get(v___y_1277_);
v_env_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref(v_env_1280_);
lean_dec(v___x_1279_);
v___x_1281_ = lean_st_ref_get(v___y_1275_);
v_mctx_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_mctx_1282_);
lean_dec(v___x_1281_);
v_lctx_1283_ = lean_ctor_get(v___y_1274_, 2);
v_options_1284_ = lean_ctor_get(v___y_1276_, 2);
lean_inc_ref(v_options_1284_);
lean_inc_ref(v_lctx_1283_);
v___x_1285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1285_, 0, v_env_1280_);
lean_ctor_set(v___x_1285_, 1, v_mctx_1282_);
lean_ctor_set(v___x_1285_, 2, v_lctx_1283_);
lean_ctor_set(v___x_1285_, 3, v_options_1284_);
v___x_1286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v_msgData_1273_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object* v_msgData_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1294_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1295_; double v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___x_1296_ = lean_float_of_nat(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_cls_1300_, lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_ref_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1353_; 
v_ref_1307_ = lean_ctor_get(v___y_1304_, 5);
v___x_1308_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1353_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1353_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v_traceState_1314_; lean_object* v_env_1315_; lean_object* v_nextMacroScope_1316_; lean_object* v_ngen_1317_; lean_object* v_auxDeclNGen_1318_; lean_object* v_cache_1319_; lean_object* v_messages_1320_; lean_object* v_infoState_1321_; lean_object* v_snapshotTasks_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1352_; 
v___x_1313_ = lean_st_ref_take(v___y_1305_);
v_traceState_1314_ = lean_ctor_get(v___x_1313_, 4);
v_env_1315_ = lean_ctor_get(v___x_1313_, 0);
v_nextMacroScope_1316_ = lean_ctor_get(v___x_1313_, 1);
v_ngen_1317_ = lean_ctor_get(v___x_1313_, 2);
v_auxDeclNGen_1318_ = lean_ctor_get(v___x_1313_, 3);
v_cache_1319_ = lean_ctor_get(v___x_1313_, 5);
v_messages_1320_ = lean_ctor_get(v___x_1313_, 6);
v_infoState_1321_ = lean_ctor_get(v___x_1313_, 7);
v_snapshotTasks_1322_ = lean_ctor_get(v___x_1313_, 8);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1324_ = v___x_1313_;
v_isShared_1325_ = v_isSharedCheck_1352_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snapshotTasks_1322_);
lean_inc(v_infoState_1321_);
lean_inc(v_messages_1320_);
lean_inc(v_cache_1319_);
lean_inc(v_traceState_1314_);
lean_inc(v_auxDeclNGen_1318_);
lean_inc(v_ngen_1317_);
lean_inc(v_nextMacroScope_1316_);
lean_inc(v_env_1315_);
lean_dec(v___x_1313_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1352_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint64_t v_tid_1326_; lean_object* v_traces_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1351_; 
v_tid_1326_ = lean_ctor_get_uint64(v_traceState_1314_, sizeof(void*)*1);
v_traces_1327_ = lean_ctor_get(v_traceState_1314_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_traceState_1314_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1329_ = v_traceState_1314_;
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_traces_1327_);
lean_dec(v_traceState_1314_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; double v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1333_ = 0;
v___x_1334_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1335_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1335_, 0, v_cls_1300_);
lean_ctor_set(v___x_1335_, 1, v___x_1331_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
lean_ctor_set_float(v___x_1335_, sizeof(void*)*3, v___x_1332_);
lean_ctor_set_float(v___x_1335_, sizeof(void*)*3 + 8, v___x_1332_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 16, v___x_1333_);
v___x_1336_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1337_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v_a_1309_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
lean_inc(v_ref_1307_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_ref_1307_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = l_Lean_PersistentArray_push___redArg(v_traces_1327_, v___x_1338_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1339_);
v___x_1341_ = v___x_1329_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1339_);
lean_ctor_set_uint64(v_reuseFailAlloc_1350_, sizeof(void*)*1, v_tid_1326_);
v___x_1341_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 4, v___x_1341_);
v___x_1343_ = v___x_1324_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_env_1315_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_nextMacroScope_1316_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_ngen_1317_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_auxDeclNGen_1318_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_cache_1319_);
lean_ctor_set(v_reuseFailAlloc_1349_, 6, v_messages_1320_);
lean_ctor_set(v_reuseFailAlloc_1349_, 7, v_infoState_1321_);
lean_ctor_set(v_reuseFailAlloc_1349_, 8, v_snapshotTasks_1322_);
v___x_1343_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = lean_st_ref_put(v___y_1305_, v___x_1343_);
v___x_1345_ = lean_box(0);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1345_);
v___x_1347_ = v___x_1311_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1354_, lean_object* v_msg_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1354_, v_msg_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1362_, lean_object* v_x_1363_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_box(0);
return v___x_1364_;
}
else
{
lean_object* v_key_1365_; lean_object* v_value_1366_; lean_object* v_tail_1367_; uint8_t v___x_1368_; 
v_key_1365_ = lean_ctor_get(v_x_1363_, 0);
v_value_1366_ = lean_ctor_get(v_x_1363_, 1);
v_tail_1367_ = lean_ctor_get(v_x_1363_, 2);
v___x_1368_ = lean_expr_eqv(v_key_1365_, v_a_1362_);
if (v___x_1368_ == 0)
{
v_x_1363_ = v_tail_1367_;
goto _start;
}
else
{
lean_object* v___x_1370_; 
lean_inc(v_value_1366_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_value_1366_);
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1371_, v_x_1372_);
lean_dec(v_x_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_buckets_1376_; lean_object* v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; uint64_t v_fold_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; uint64_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_buckets_1376_ = lean_ctor_get(v_m_1374_, 1);
v___x_1377_ = lean_array_get_size(v_buckets_1376_);
v___x_1378_ = l_Lean_Expr_hash(v_a_1375_);
v___x_1379_ = 32ULL;
v___x_1380_ = lean_uint64_shift_right(v___x_1378_, v___x_1379_);
v_fold_1381_ = lean_uint64_xor(v___x_1378_, v___x_1380_);
v___x_1382_ = 16ULL;
v___x_1383_ = lean_uint64_shift_right(v_fold_1381_, v___x_1382_);
v___x_1384_ = lean_uint64_xor(v_fold_1381_, v___x_1383_);
v___x_1385_ = lean_uint64_to_usize(v___x_1384_);
v___x_1386_ = lean_usize_of_nat(v___x_1377_);
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_sub(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_usize_land(v___x_1385_, v___x_1388_);
v___x_1390_ = lean_array_uget_borrowed(v_buckets_1376_, v___x_1389_);
v___x_1391_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1375_, v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1392_, v_a_1393_);
lean_dec_ref(v_a_1393_);
lean_dec_ref(v_m_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1395_, lean_object* v_type_1396_, lean_object* v_val_1397_, lean_object* v_k_1398_, uint8_t v_nondep_1399_, uint8_t v_kind_1400_, uint8_t v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_box(v___y_1401_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1410_, 0, v_k_1398_);
lean_closure_set(v___f_1410_, 1, v___x_1409_);
lean_closure_set(v___f_1410_, 2, v___y_1402_);
lean_closure_set(v___f_1410_, 3, v___y_1403_);
v___x_1411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1395_, v_type_1396_, v_val_1397_, v___f_1410_, v_nondep_1399_, v_kind_1400_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1411_) == 0)
{
return v___x_1411_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1420_, lean_object* v_type_1421_, lean_object* v_val_1422_, lean_object* v_k_1423_, lean_object* v_nondep_1424_, lean_object* v_kind_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v_nondep_boxed_1434_; uint8_t v_kind_boxed_1435_; uint8_t v___y_68234__boxed_1436_; lean_object* v_res_1437_; 
v_nondep_boxed_1434_ = lean_unbox(v_nondep_1424_);
v_kind_boxed_1435_ = lean_unbox(v_kind_1425_);
v___y_68234__boxed_1436_ = lean_unbox(v___y_1426_);
v_res_1437_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1420_, v_type_1421_, v_val_1422_, v_k_1423_, v_nondep_boxed_1434_, v_kind_boxed_1435_, v___y_68234__boxed_1436_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = l_Lean_instInhabitedExpr;
v___x_1440_ = lean_panic_fn_borrowed(v___x_1439_, v_msg_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1443_, lean_object* v_body_1444_, lean_object* v_x_1445_, uint8_t v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_array_push(v_fvars_1443_, v_x_1445_);
v___x_1455_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1454_, v_body_1444_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1456_, lean_object* v_body_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v___y_68397__boxed_1467_; lean_object* v_res_1468_; 
v___y_68397__boxed_1467_ = lean_unbox(v___y_1459_);
v_res_1468_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1456_, v_body_1457_, v_x_1458_, v___y_68397__boxed_1467_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1469_, lean_object* v_e_1470_, uint8_t v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
if (lean_obj_tag(v_e_1470_) == 6)
{
lean_object* v_binderName_1479_; lean_object* v_binderType_1480_; lean_object* v_body_1481_; uint8_t v_binderInfo_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_binderName_1479_ = lean_ctor_get(v_e_1470_, 0);
lean_inc(v_binderName_1479_);
v_binderType_1480_ = lean_ctor_get(v_e_1470_, 1);
lean_inc_ref(v_binderType_1480_);
v_body_1481_ = lean_ctor_get(v_e_1470_, 2);
lean_inc_ref(v_body_1481_);
v_binderInfo_1482_ = lean_ctor_get_uint8(v_e_1470_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1470_, 3);
v___x_1483_ = lean_expr_instantiate_rev(v_binderType_1480_, v_fvars_1469_);
lean_dec_ref(v_binderType_1480_);
v___x_1484_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1483_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___f_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___f_1486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1486_, 0, v_fvars_1469_);
lean_closure_set(v___f_1486_, 1, v_body_1481_);
v___x_1487_ = 0;
v___x_1488_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1479_, v_binderInfo_1482_, v_a_1485_, v___f_1486_, v___x_1487_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1488_;
}
else
{
lean_dec_ref(v_body_1481_);
lean_dec(v_binderName_1479_);
lean_dec_ref(v_fvars_1469_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_expr_instantiate_rev(v_e_1470_, v_fvars_1469_);
lean_dec_ref(v_e_1470_);
v___x_1490_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1489_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; uint8_t v___x_1492_; uint8_t v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = 0;
v___x_1493_ = 1;
v___x_1494_ = 1;
v___x_1495_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1469_, v_a_1491_, v___x_1492_, v___x_1493_, v___x_1492_, v___x_1493_, v___x_1494_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec_ref(v_fvars_1469_);
return v___x_1495_;
}
else
{
lean_dec_ref(v_fvars_1469_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1496_, uint8_t v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
if (v_a_1497_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1506_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1505_, v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1508_ = l_Lean_Meta_Sym_etaReduce(v_e_1496_);
lean_dec_ref(v_e_1496_);
v___x_1509_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1507_, v___x_1508_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1510_, lean_object* v_body_1511_, lean_object* v_x_1512_, uint8_t v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_array_push(v_fvars_1510_, v_x_1512_);
v___x_1522_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1521_, v_body_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1523_, lean_object* v_body_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v___y_68408__boxed_1534_; lean_object* v_res_1535_; 
v___y_68408__boxed_1534_ = lean_unbox(v___y_1526_);
v_res_1535_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1523_, v_body_1524_, v_x_1525_, v___y_68408__boxed_1534_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1536_, lean_object* v_e_1537_, uint8_t v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
if (lean_obj_tag(v_e_1537_) == 8)
{
lean_object* v_declName_1546_; lean_object* v_type_1547_; lean_object* v_value_1548_; lean_object* v_body_1549_; uint8_t v_nondep_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_declName_1546_ = lean_ctor_get(v_e_1537_, 0);
lean_inc(v_declName_1546_);
v_type_1547_ = lean_ctor_get(v_e_1537_, 1);
lean_inc_ref(v_type_1547_);
v_value_1548_ = lean_ctor_get(v_e_1537_, 2);
lean_inc_ref(v_value_1548_);
v_body_1549_ = lean_ctor_get(v_e_1537_, 3);
lean_inc_ref(v_body_1549_);
v_nondep_1550_ = lean_ctor_get_uint8(v_e_1537_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1537_, 4);
v___x_1551_ = lean_expr_instantiate_rev(v_type_1547_, v_fvars_1536_);
lean_dec_ref(v_type_1547_);
v___x_1552_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1551_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = lean_expr_instantiate_rev(v_value_1548_, v_fvars_1536_);
lean_dec_ref(v_value_1548_);
v___x_1555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1554_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___f_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1557_, 0, v_fvars_1536_);
lean_closure_set(v___f_1557_, 1, v_body_1549_);
v___x_1558_ = 0;
v___x_1559_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1546_, v_a_1553_, v_a_1556_, v___f_1557_, v_nondep_1550_, v___x_1558_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v___x_1559_;
}
else
{
lean_dec(v_a_1553_);
lean_dec_ref(v_body_1549_);
lean_dec(v_declName_1546_);
lean_dec_ref(v_fvars_1536_);
return v___x_1555_;
}
}
else
{
lean_dec_ref(v_body_1549_);
lean_dec_ref(v_value_1548_);
lean_dec(v_declName_1546_);
lean_dec_ref(v_fvars_1536_);
return v___x_1552_;
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_expr_instantiate_rev(v_e_1537_, v_fvars_1536_);
lean_dec_ref(v_e_1537_);
v___x_1561_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1560_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; uint8_t v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = 1;
v___x_1564_ = 0;
v___x_1565_ = 1;
v___x_1566_ = l_Lean_Meta_mkLetFVars(v_fvars_1536_, v_a_1562_, v___x_1563_, v___x_1564_, v___x_1565_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
lean_dec_ref(v_fvars_1536_);
return v___x_1566_;
}
else
{
lean_dec_ref(v_fvars_1536_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1567_, uint8_t v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
if (v_a_1568_ == 0)
{
uint8_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = 1;
v___x_1577_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1567_, v___x_1576_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
return v___x_1577_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1579_, uint8_t v_report_1580_, uint8_t v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1589_; 
lean_inc(v_a_1587_);
lean_inc_ref(v_a_1586_);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc_ref(v_e_1579_);
v___x_1589_ = lean_infer_type(v_e_1579_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc_n(v_a_1590_, 2);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Meta_isProp(v_a_1590_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1604_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
if (v_a_1581_ == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_unbox(v_a_1592_);
lean_dec(v_a_1592_);
if (v___x_1600_ == 0)
{
lean_del_object(v___x_1594_);
goto v___jp_1596_;
}
else
{
lean_object* v___x_1602_; 
lean_dec(v_a_1590_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v_e_1579_);
v___x_1602_ = v___x_1594_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_e_1579_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_del_object(v___x_1594_);
lean_dec(v_a_1592_);
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1590_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1599_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1579_, v_a_1598_, v_report_1580_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1599_;
}
else
{
lean_dec_ref(v_e_1579_);
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1579_);
v_a_1605_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1591_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1591_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_dec_ref(v_e_1579_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1613_, uint8_t v_report_1614_, uint8_t v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
if (v_a_1615_ == 0)
{
lean_object* v___x_1623_; lean_object* v_canon_1624_; lean_object* v_cache_1625_; lean_object* v___x_1626_; 
v___x_1623_ = lean_st_ref_get(v_a_1617_);
v_canon_1624_ = lean_ctor_get(v___x_1623_, 9);
lean_inc_ref(v_canon_1624_);
lean_dec(v___x_1623_);
v_cache_1625_ = lean_ctor_get(v_canon_1624_, 0);
lean_inc_ref(v_cache_1625_);
lean_dec_ref(v_canon_1624_);
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1625_, v_e_1613_);
lean_dec_ref(v_cache_1625_);
if (lean_obj_tag(v___x_1626_) == 1)
{
lean_object* v_val_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_e_1613_);
v_val_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_val_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_val_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v___x_1635_; 
lean_dec(v___x_1626_);
lean_inc_ref(v_e_1613_);
v___x_1635_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1613_, v_report_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1674_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1674_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1674_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v_canon_1641_; lean_object* v_share_1642_; lean_object* v_maxFVar_1643_; lean_object* v_proofInstInfo_1644_; lean_object* v_inferType_1645_; lean_object* v_getLevel_1646_; lean_object* v_congrInfo_1647_; lean_object* v_defEqI_1648_; lean_object* v_extensions_1649_; lean_object* v_issues_1650_; lean_object* v_instanceOverrides_1651_; uint8_t v_debug_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1673_; 
v___x_1640_ = lean_st_ref_take(v_a_1617_);
v_canon_1641_ = lean_ctor_get(v___x_1640_, 9);
v_share_1642_ = lean_ctor_get(v___x_1640_, 0);
v_maxFVar_1643_ = lean_ctor_get(v___x_1640_, 1);
v_proofInstInfo_1644_ = lean_ctor_get(v___x_1640_, 2);
v_inferType_1645_ = lean_ctor_get(v___x_1640_, 3);
v_getLevel_1646_ = lean_ctor_get(v___x_1640_, 4);
v_congrInfo_1647_ = lean_ctor_get(v___x_1640_, 5);
v_defEqI_1648_ = lean_ctor_get(v___x_1640_, 6);
v_extensions_1649_ = lean_ctor_get(v___x_1640_, 7);
v_issues_1650_ = lean_ctor_get(v___x_1640_, 8);
v_instanceOverrides_1651_ = lean_ctor_get(v___x_1640_, 10);
v_debug_1652_ = lean_ctor_get_uint8(v___x_1640_, sizeof(void*)*11);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1654_ = v___x_1640_;
v_isShared_1655_ = v_isSharedCheck_1673_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_instanceOverrides_1651_);
lean_inc(v_canon_1641_);
lean_inc(v_issues_1650_);
lean_inc(v_extensions_1649_);
lean_inc(v_defEqI_1648_);
lean_inc(v_congrInfo_1647_);
lean_inc(v_getLevel_1646_);
lean_inc(v_inferType_1645_);
lean_inc(v_proofInstInfo_1644_);
lean_inc(v_maxFVar_1643_);
lean_inc(v_share_1642_);
lean_dec(v___x_1640_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1673_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_cache_1656_; lean_object* v_cacheInType_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1672_; 
v_cache_1656_ = lean_ctor_get(v_canon_1641_, 0);
v_cacheInType_1657_ = lean_ctor_get(v_canon_1641_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_canon_1641_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1659_ = v_canon_1641_;
v_isShared_1660_ = v_isSharedCheck_1672_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_cacheInType_1657_);
lean_inc(v_cache_1656_);
lean_dec(v_canon_1641_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1672_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_inc(v_a_1636_);
v___x_1661_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1656_, v_e_1613_, v_a_1636_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_cacheInType_1657_);
v___x_1663_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 9, v___x_1663_);
v___x_1665_ = v___x_1654_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_share_1642_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_maxFVar_1643_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_proofInstInfo_1644_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_inferType_1645_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_getLevel_1646_);
lean_ctor_set(v_reuseFailAlloc_1670_, 5, v_congrInfo_1647_);
lean_ctor_set(v_reuseFailAlloc_1670_, 6, v_defEqI_1648_);
lean_ctor_set(v_reuseFailAlloc_1670_, 7, v_extensions_1649_);
lean_ctor_set(v_reuseFailAlloc_1670_, 8, v_issues_1650_);
lean_ctor_set(v_reuseFailAlloc_1670_, 9, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1670_, 10, v_instanceOverrides_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*11, v_debug_1652_);
v___x_1665_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_st_ref_put(v_a_1617_, v___x_1665_);
if (v_isShared_1639_ == 0)
{
v___x_1668_ = v___x_1638_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1636_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1613_);
return v___x_1635_;
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v_canon_1676_; lean_object* v_cacheInType_1677_; lean_object* v___x_1678_; 
v___x_1675_ = lean_st_ref_get(v_a_1617_);
v_canon_1676_ = lean_ctor_get(v___x_1675_, 9);
lean_inc_ref(v_canon_1676_);
lean_dec(v___x_1675_);
v_cacheInType_1677_ = lean_ctor_get(v_canon_1676_, 1);
lean_inc_ref(v_cacheInType_1677_);
lean_dec_ref(v_canon_1676_);
v___x_1678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1677_, v_e_1613_);
lean_dec_ref(v_cacheInType_1677_);
if (lean_obj_tag(v___x_1678_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_e_1613_);
v_val_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_val_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_object* v___x_1687_; 
lean_dec(v___x_1678_);
lean_inc_ref(v_e_1613_);
v___x_1687_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1613_, v_report_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1726_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1726_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1726_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v_canon_1693_; lean_object* v_share_1694_; lean_object* v_maxFVar_1695_; lean_object* v_proofInstInfo_1696_; lean_object* v_inferType_1697_; lean_object* v_getLevel_1698_; lean_object* v_congrInfo_1699_; lean_object* v_defEqI_1700_; lean_object* v_extensions_1701_; lean_object* v_issues_1702_; lean_object* v_instanceOverrides_1703_; uint8_t v_debug_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1725_; 
v___x_1692_ = lean_st_ref_take(v_a_1617_);
v_canon_1693_ = lean_ctor_get(v___x_1692_, 9);
v_share_1694_ = lean_ctor_get(v___x_1692_, 0);
v_maxFVar_1695_ = lean_ctor_get(v___x_1692_, 1);
v_proofInstInfo_1696_ = lean_ctor_get(v___x_1692_, 2);
v_inferType_1697_ = lean_ctor_get(v___x_1692_, 3);
v_getLevel_1698_ = lean_ctor_get(v___x_1692_, 4);
v_congrInfo_1699_ = lean_ctor_get(v___x_1692_, 5);
v_defEqI_1700_ = lean_ctor_get(v___x_1692_, 6);
v_extensions_1701_ = lean_ctor_get(v___x_1692_, 7);
v_issues_1702_ = lean_ctor_get(v___x_1692_, 8);
v_instanceOverrides_1703_ = lean_ctor_get(v___x_1692_, 10);
v_debug_1704_ = lean_ctor_get_uint8(v___x_1692_, sizeof(void*)*11);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1706_ = v___x_1692_;
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_instanceOverrides_1703_);
lean_inc(v_canon_1693_);
lean_inc(v_issues_1702_);
lean_inc(v_extensions_1701_);
lean_inc(v_defEqI_1700_);
lean_inc(v_congrInfo_1699_);
lean_inc(v_getLevel_1698_);
lean_inc(v_inferType_1697_);
lean_inc(v_proofInstInfo_1696_);
lean_inc(v_maxFVar_1695_);
lean_inc(v_share_1694_);
lean_dec(v___x_1692_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_cache_1708_; lean_object* v_cacheInType_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1724_; 
v_cache_1708_ = lean_ctor_get(v_canon_1693_, 0);
v_cacheInType_1709_ = lean_ctor_get(v_canon_1693_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_canon_1693_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1711_ = v_canon_1693_;
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_cacheInType_1709_);
lean_inc(v_cache_1708_);
lean_dec(v_canon_1693_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc(v_a_1688_);
v___x_1713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1709_, v_e_1613_, v_a_1688_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_cache_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 9, v___x_1715_);
v___x_1717_ = v___x_1706_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_share_1694_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_maxFVar_1695_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_proofInstInfo_1696_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_inferType_1697_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_getLevel_1698_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_congrInfo_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_defEqI_1700_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_extensions_1701_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_issues_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1722_, 10, v_instanceOverrides_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*11, v_debug_1704_);
v___x_1717_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_st_ref_put(v_a_1617_, v___x_1717_);
if (v_isShared_1691_ == 0)
{
v___x_1720_ = v___x_1690_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1688_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1613_);
return v___x_1687_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1743_ = l_Lean_mkConst(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1744_, lean_object* v_prop_1745_, lean_object* v_inst_1746_, lean_object* v_e_1747_, uint8_t v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; 
lean_inc_ref(v_prop_1745_);
v___x_1756_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1745_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1796_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1796_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1796_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1757_);
v___x_1772_ = l_Lean_Expr_app___override(v___x_1771_, v_a_1757_);
if (v_a_1748_ == 0)
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1772_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___y_1776_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
if (lean_obj_tag(v_a_1774_) == 0)
{
lean_inc_ref(v_inst_1746_);
v___y_1776_ = v_inst_1746_;
goto v___jp_1775_;
}
else
{
lean_object* v_val_1785_; 
v_val_1785_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v_a_1774_, 1);
v___y_1776_ = v_val_1785_;
goto v___jp_1775_;
}
v___jp_1775_:
{
lean_object* v___x_1777_; 
lean_inc_ref(v_inst_1746_);
v___x_1777_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1746_, v___y_1776_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; size_t v___x_1779_; size_t v___x_1780_; uint8_t v___x_1781_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = lean_ptr_addr(v_prop_1745_);
lean_dec_ref(v_prop_1745_);
v___x_1780_ = lean_ptr_addr(v_a_1757_);
v___x_1781_ = lean_usize_dec_eq(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_inst_1746_);
v___y_1762_ = v_a_1778_;
v___y_1763_ = v___x_1781_;
goto v___jp_1761_;
}
else
{
size_t v___x_1782_; size_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_ptr_addr(v_inst_1746_);
lean_dec_ref(v_inst_1746_);
v___x_1783_ = lean_ptr_addr(v_a_1778_);
v___x_1784_ = lean_usize_dec_eq(v___x_1782_, v___x_1783_);
v___y_1762_ = v_a_1778_;
v___y_1763_ = v___x_1784_;
goto v___jp_1761_;
}
}
else
{
lean_del_object(v___x_1759_);
lean_dec(v_a_1757_);
lean_dec_ref(v_e_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_prop_1745_);
lean_dec_ref(v_g_1744_);
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_del_object(v___x_1759_);
lean_dec(v_a_1757_);
lean_dec_ref(v_e_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_prop_1745_);
lean_dec_ref(v_g_1744_);
v_a_1786_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1773_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1773_);
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
uint8_t v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1759_);
lean_dec(v_a_1757_);
lean_dec_ref(v_e_1747_);
lean_dec_ref(v_prop_1745_);
lean_dec_ref(v_g_1744_);
v___x_1794_ = 0;
v___x_1795_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1746_, v___x_1772_, v___x_1794_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
return v___x_1795_;
}
v___jp_1761_:
{
if (v___y_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec_ref(v_e_1747_);
v___x_1764_ = l_Lean_mkAppB(v_g_1744_, v_a_1757_, v___y_1762_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1764_);
v___x_1766_ = v___x_1759_;
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
lean_object* v___x_1769_; 
lean_dec_ref(v___y_1762_);
lean_dec(v_a_1757_);
lean_dec_ref(v_g_1744_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v_e_1747_);
v___x_1769_ = v___x_1759_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_e_1747_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_prop_1745_);
lean_dec_ref(v_g_1744_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1797_, lean_object* v_prop_1798_, lean_object* v_h_1799_, lean_object* v_e_1800_, uint8_t v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
if (v_a_1801_ == 0)
{
lean_object* v___x_1809_; lean_object* v_canon_1810_; lean_object* v_cache_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_st_ref_get(v_a_1803_);
v_canon_1810_ = lean_ctor_get(v___x_1809_, 9);
lean_inc_ref(v_canon_1810_);
lean_dec(v___x_1809_);
v_cache_1811_ = lean_ctor_get(v_canon_1810_, 0);
lean_inc_ref(v_cache_1811_);
lean_dec_ref(v_canon_1810_);
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1811_, v_e_1800_);
lean_dec_ref(v_cache_1811_);
if (lean_obj_tag(v___x_1812_) == 1)
{
lean_object* v_val_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_e_1800_);
lean_dec_ref(v_h_1799_);
lean_dec_ref(v_prop_1798_);
lean_dec_ref(v_g_1797_);
v_val_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_val_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 0);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_val_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec(v___x_1812_);
lean_inc_ref(v_e_1800_);
v___x_1821_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1797_, v_prop_1798_, v_h_1799_, v_e_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1860_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1860_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1860_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v_canon_1827_; lean_object* v_share_1828_; lean_object* v_maxFVar_1829_; lean_object* v_proofInstInfo_1830_; lean_object* v_inferType_1831_; lean_object* v_getLevel_1832_; lean_object* v_congrInfo_1833_; lean_object* v_defEqI_1834_; lean_object* v_extensions_1835_; lean_object* v_issues_1836_; lean_object* v_instanceOverrides_1837_; uint8_t v_debug_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1859_; 
v___x_1826_ = lean_st_ref_take(v_a_1803_);
v_canon_1827_ = lean_ctor_get(v___x_1826_, 9);
v_share_1828_ = lean_ctor_get(v___x_1826_, 0);
v_maxFVar_1829_ = lean_ctor_get(v___x_1826_, 1);
v_proofInstInfo_1830_ = lean_ctor_get(v___x_1826_, 2);
v_inferType_1831_ = lean_ctor_get(v___x_1826_, 3);
v_getLevel_1832_ = lean_ctor_get(v___x_1826_, 4);
v_congrInfo_1833_ = lean_ctor_get(v___x_1826_, 5);
v_defEqI_1834_ = lean_ctor_get(v___x_1826_, 6);
v_extensions_1835_ = lean_ctor_get(v___x_1826_, 7);
v_issues_1836_ = lean_ctor_get(v___x_1826_, 8);
v_instanceOverrides_1837_ = lean_ctor_get(v___x_1826_, 10);
v_debug_1838_ = lean_ctor_get_uint8(v___x_1826_, sizeof(void*)*11);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1840_ = v___x_1826_;
v_isShared_1841_ = v_isSharedCheck_1859_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_instanceOverrides_1837_);
lean_inc(v_canon_1827_);
lean_inc(v_issues_1836_);
lean_inc(v_extensions_1835_);
lean_inc(v_defEqI_1834_);
lean_inc(v_congrInfo_1833_);
lean_inc(v_getLevel_1832_);
lean_inc(v_inferType_1831_);
lean_inc(v_proofInstInfo_1830_);
lean_inc(v_maxFVar_1829_);
lean_inc(v_share_1828_);
lean_dec(v___x_1826_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1859_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_cache_1842_; lean_object* v_cacheInType_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1858_; 
v_cache_1842_ = lean_ctor_get(v_canon_1827_, 0);
v_cacheInType_1843_ = lean_ctor_get(v_canon_1827_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_canon_1827_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1845_ = v_canon_1827_;
v_isShared_1846_ = v_isSharedCheck_1858_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_cacheInType_1843_);
lean_inc(v_cache_1842_);
lean_dec(v_canon_1827_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1858_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_inc(v_a_1822_);
v___x_1847_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1842_, v_e_1800_, v_a_1822_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_cacheInType_1843_);
v___x_1849_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 9, v___x_1849_);
v___x_1851_ = v___x_1840_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_share_1828_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_maxFVar_1829_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_proofInstInfo_1830_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_inferType_1831_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_getLevel_1832_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_congrInfo_1833_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_defEqI_1834_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_extensions_1835_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_issues_1836_);
lean_ctor_set(v_reuseFailAlloc_1856_, 9, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1856_, 10, v_instanceOverrides_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*11, v_debug_1838_);
v___x_1851_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_st_ref_put(v_a_1803_, v___x_1851_);
if (v_isShared_1825_ == 0)
{
v___x_1854_ = v___x_1824_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1822_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1800_);
return v___x_1821_;
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v_canon_1862_; lean_object* v_cacheInType_1863_; lean_object* v___x_1864_; 
v___x_1861_ = lean_st_ref_get(v_a_1803_);
v_canon_1862_ = lean_ctor_get(v___x_1861_, 9);
lean_inc_ref(v_canon_1862_);
lean_dec(v___x_1861_);
v_cacheInType_1863_ = lean_ctor_get(v_canon_1862_, 1);
lean_inc_ref(v_cacheInType_1863_);
lean_dec_ref(v_canon_1862_);
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1863_, v_e_1800_);
lean_dec_ref(v_cacheInType_1863_);
if (lean_obj_tag(v___x_1864_) == 1)
{
lean_object* v_val_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v_e_1800_);
lean_dec_ref(v_h_1799_);
lean_dec_ref(v_prop_1798_);
lean_dec_ref(v_g_1797_);
v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_val_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 0);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v___x_1864_);
lean_inc_ref(v_e_1800_);
v___x_1873_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1797_, v_prop_1798_, v_h_1799_, v_e_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1912_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1912_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1912_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v_canon_1879_; lean_object* v_share_1880_; lean_object* v_maxFVar_1881_; lean_object* v_proofInstInfo_1882_; lean_object* v_inferType_1883_; lean_object* v_getLevel_1884_; lean_object* v_congrInfo_1885_; lean_object* v_defEqI_1886_; lean_object* v_extensions_1887_; lean_object* v_issues_1888_; lean_object* v_instanceOverrides_1889_; uint8_t v_debug_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1911_; 
v___x_1878_ = lean_st_ref_take(v_a_1803_);
v_canon_1879_ = lean_ctor_get(v___x_1878_, 9);
v_share_1880_ = lean_ctor_get(v___x_1878_, 0);
v_maxFVar_1881_ = lean_ctor_get(v___x_1878_, 1);
v_proofInstInfo_1882_ = lean_ctor_get(v___x_1878_, 2);
v_inferType_1883_ = lean_ctor_get(v___x_1878_, 3);
v_getLevel_1884_ = lean_ctor_get(v___x_1878_, 4);
v_congrInfo_1885_ = lean_ctor_get(v___x_1878_, 5);
v_defEqI_1886_ = lean_ctor_get(v___x_1878_, 6);
v_extensions_1887_ = lean_ctor_get(v___x_1878_, 7);
v_issues_1888_ = lean_ctor_get(v___x_1878_, 8);
v_instanceOverrides_1889_ = lean_ctor_get(v___x_1878_, 10);
v_debug_1890_ = lean_ctor_get_uint8(v___x_1878_, sizeof(void*)*11);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1892_ = v___x_1878_;
v_isShared_1893_ = v_isSharedCheck_1911_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_instanceOverrides_1889_);
lean_inc(v_canon_1879_);
lean_inc(v_issues_1888_);
lean_inc(v_extensions_1887_);
lean_inc(v_defEqI_1886_);
lean_inc(v_congrInfo_1885_);
lean_inc(v_getLevel_1884_);
lean_inc(v_inferType_1883_);
lean_inc(v_proofInstInfo_1882_);
lean_inc(v_maxFVar_1881_);
lean_inc(v_share_1880_);
lean_dec(v___x_1878_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1911_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_cache_1894_; lean_object* v_cacheInType_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1910_; 
v_cache_1894_ = lean_ctor_get(v_canon_1879_, 0);
v_cacheInType_1895_ = lean_ctor_get(v_canon_1879_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_canon_1879_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1897_ = v_canon_1879_;
v_isShared_1898_ = v_isSharedCheck_1910_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_cacheInType_1895_);
lean_inc(v_cache_1894_);
lean_dec(v_canon_1879_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1910_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_inc(v_a_1874_);
v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1895_, v_e_1800_, v_a_1874_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_cache_1894_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 9, v___x_1901_);
v___x_1903_ = v___x_1892_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_share_1880_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_maxFVar_1881_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_proofInstInfo_1882_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v_inferType_1883_);
lean_ctor_set(v_reuseFailAlloc_1908_, 4, v_getLevel_1884_);
lean_ctor_set(v_reuseFailAlloc_1908_, 5, v_congrInfo_1885_);
lean_ctor_set(v_reuseFailAlloc_1908_, 6, v_defEqI_1886_);
lean_ctor_set(v_reuseFailAlloc_1908_, 7, v_extensions_1887_);
lean_ctor_set(v_reuseFailAlloc_1908_, 8, v_issues_1888_);
lean_ctor_set(v_reuseFailAlloc_1908_, 9, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1908_, 10, v_instanceOverrides_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1908_, sizeof(void*)*11, v_debug_1890_);
v___x_1903_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_st_ref_put(v_a_1803_, v___x_1903_);
if (v_isShared_1877_ == 0)
{
v___x_1906_ = v___x_1876_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1874_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1800_);
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1913_, lean_object* v_prop_1914_, lean_object* v_h_1915_, lean_object* v_e_1916_, uint8_t v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_a_1926_; lean_object* v___y_1960_; 
if (v_a_1917_ == 0)
{
lean_object* v___x_2000_; lean_object* v_canon_2001_; lean_object* v_cache_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_st_ref_get(v_a_1919_);
v_canon_2001_ = lean_ctor_get(v___x_2000_, 9);
lean_inc_ref(v_canon_2001_);
lean_dec(v___x_2000_);
v_cache_2002_ = lean_ctor_get(v_canon_2001_, 0);
lean_inc_ref(v_cache_2002_);
lean_dec_ref(v_canon_2001_);
v___x_2003_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2002_, v_e_1916_);
lean_dec_ref(v_cache_2002_);
if (lean_obj_tag(v___x_2003_) == 1)
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_e_1916_);
lean_dec_ref(v_h_1915_);
lean_dec_ref(v_prop_1914_);
lean_dec_ref(v_g_1913_);
v_val_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 0);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v___x_2003_);
lean_inc_ref(v_prop_1914_);
v___x_2012_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1914_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_n(v_a_2013_, 2);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2013_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2021_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
if (lean_obj_tag(v_a_2015_) == 0)
{
lean_inc_ref(v_h_1915_);
v___y_2021_ = v_h_1915_;
goto v___jp_2020_;
}
else
{
lean_object* v_val_2028_; 
v_val_2028_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_val_2028_);
lean_dec_ref_known(v_a_2015_, 1);
v___y_2021_ = v_val_2028_;
goto v___jp_2020_;
}
v___jp_2016_:
{
if (v___y_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_mkAppB(v_g_1913_, v_a_2013_, v___y_2017_);
v_a_1926_ = v___x_2019_;
goto v___jp_1925_;
}
else
{
lean_dec_ref(v___y_2017_);
lean_dec(v_a_2013_);
lean_dec_ref(v_g_1913_);
lean_inc_ref(v_e_1916_);
v_a_1926_ = v_e_1916_;
goto v___jp_1925_;
}
}
v___jp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_ptr_addr(v_prop_1914_);
lean_dec_ref(v_prop_1914_);
v___x_2023_ = lean_ptr_addr(v_a_2013_);
v___x_2024_ = lean_usize_dec_eq(v___x_2022_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v_h_1915_);
v___y_2017_ = v___y_2021_;
v___y_2018_ = v___x_2024_;
goto v___jp_2016_;
}
else
{
size_t v___x_2025_; size_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_ptr_addr(v_h_1915_);
lean_dec_ref(v_h_1915_);
v___x_2026_ = lean_ptr_addr(v___y_2021_);
v___x_2027_ = lean_usize_dec_eq(v___x_2025_, v___x_2026_);
v___y_2017_ = v___y_2021_;
v___y_2018_ = v___x_2027_;
goto v___jp_2016_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_2013_);
lean_dec_ref(v_e_1916_);
lean_dec_ref(v_h_1915_);
lean_dec_ref(v_prop_1914_);
lean_dec_ref(v_g_1913_);
v_a_2029_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2014_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2014_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_dec_ref(v_h_1915_);
lean_dec_ref(v_prop_1914_);
lean_dec_ref(v_g_1913_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2012_, 1);
v_a_1926_ = v_a_2037_;
goto v___jp_1925_;
}
else
{
lean_dec_ref(v_e_1916_);
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v_canon_2039_; lean_object* v_cacheInType_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v_g_1913_);
v___x_2038_ = lean_st_ref_get(v_a_1919_);
v_canon_2039_ = lean_ctor_get(v___x_2038_, 9);
lean_inc_ref(v_canon_2039_);
lean_dec(v___x_2038_);
v_cacheInType_2040_ = lean_ctor_get(v_canon_2039_, 1);
lean_inc_ref(v_cacheInType_2040_);
lean_dec_ref(v_canon_2039_);
v___x_2041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2040_, v_e_1916_);
lean_dec_ref(v_cacheInType_2040_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_e_1916_);
lean_dec_ref(v_h_1915_);
lean_dec_ref(v_prop_1914_);
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
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
lean_ctor_set_tag(v___x_2044_, 0);
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
lean_object* v___x_2050_; 
lean_dec(v___x_2041_);
v___x_2050_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1914_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = 0;
v___x_2053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1915_, v_a_2051_, v___x_2052_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
v___y_1960_ = v___x_2053_;
goto v___jp_1959_;
}
else
{
lean_dec_ref(v_h_1915_);
v___y_1960_ = v___x_2050_;
goto v___jp_1959_;
}
}
}
v___jp_1925_:
{
lean_object* v___x_1927_; lean_object* v_canon_1928_; lean_object* v_share_1929_; lean_object* v_maxFVar_1930_; lean_object* v_proofInstInfo_1931_; lean_object* v_inferType_1932_; lean_object* v_getLevel_1933_; lean_object* v_congrInfo_1934_; lean_object* v_defEqI_1935_; lean_object* v_extensions_1936_; lean_object* v_issues_1937_; lean_object* v_instanceOverrides_1938_; uint8_t v_debug_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1958_; 
v___x_1927_ = lean_st_ref_take(v_a_1919_);
v_canon_1928_ = lean_ctor_get(v___x_1927_, 9);
v_share_1929_ = lean_ctor_get(v___x_1927_, 0);
v_maxFVar_1930_ = lean_ctor_get(v___x_1927_, 1);
v_proofInstInfo_1931_ = lean_ctor_get(v___x_1927_, 2);
v_inferType_1932_ = lean_ctor_get(v___x_1927_, 3);
v_getLevel_1933_ = lean_ctor_get(v___x_1927_, 4);
v_congrInfo_1934_ = lean_ctor_get(v___x_1927_, 5);
v_defEqI_1935_ = lean_ctor_get(v___x_1927_, 6);
v_extensions_1936_ = lean_ctor_get(v___x_1927_, 7);
v_issues_1937_ = lean_ctor_get(v___x_1927_, 8);
v_instanceOverrides_1938_ = lean_ctor_get(v___x_1927_, 10);
v_debug_1939_ = lean_ctor_get_uint8(v___x_1927_, sizeof(void*)*11);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1941_ = v___x_1927_;
v_isShared_1942_ = v_isSharedCheck_1958_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_instanceOverrides_1938_);
lean_inc(v_canon_1928_);
lean_inc(v_issues_1937_);
lean_inc(v_extensions_1936_);
lean_inc(v_defEqI_1935_);
lean_inc(v_congrInfo_1934_);
lean_inc(v_getLevel_1933_);
lean_inc(v_inferType_1932_);
lean_inc(v_proofInstInfo_1931_);
lean_inc(v_maxFVar_1930_);
lean_inc(v_share_1929_);
lean_dec(v___x_1927_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1958_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_cache_1943_; lean_object* v_cacheInType_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1957_; 
v_cache_1943_ = lean_ctor_get(v_canon_1928_, 0);
v_cacheInType_1944_ = lean_ctor_get(v_canon_1928_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_canon_1928_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1946_ = v_canon_1928_;
v_isShared_1947_ = v_isSharedCheck_1957_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_cacheInType_1944_);
lean_inc(v_cache_1943_);
lean_dec(v_canon_1928_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1957_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_inc_ref(v_a_1926_);
v___x_1948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1943_, v_e_1916_, v_a_1926_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_cacheInType_1944_);
v___x_1950_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1952_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 9, v___x_1950_);
v___x_1952_ = v___x_1941_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_share_1929_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_maxFVar_1930_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_proofInstInfo_1931_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_inferType_1932_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_getLevel_1933_);
lean_ctor_set(v_reuseFailAlloc_1955_, 5, v_congrInfo_1934_);
lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_defEqI_1935_);
lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_extensions_1936_);
lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_issues_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 9, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1955_, 10, v_instanceOverrides_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*11, v_debug_1939_);
v___x_1952_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_st_ref_put(v_a_1919_, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_a_1926_);
return v___x_1954_;
}
}
}
}
}
v___jp_1959_:
{
if (lean_obj_tag(v___y_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1999_; 
v_a_1961_ = lean_ctor_get(v___y_1960_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___y_1960_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1963_ = v___y_1960_;
v_isShared_1964_ = v_isSharedCheck_1999_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___y_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1999_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v_canon_1966_; lean_object* v_share_1967_; lean_object* v_maxFVar_1968_; lean_object* v_proofInstInfo_1969_; lean_object* v_inferType_1970_; lean_object* v_getLevel_1971_; lean_object* v_congrInfo_1972_; lean_object* v_defEqI_1973_; lean_object* v_extensions_1974_; lean_object* v_issues_1975_; lean_object* v_instanceOverrides_1976_; uint8_t v_debug_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1998_; 
v___x_1965_ = lean_st_ref_take(v_a_1919_);
v_canon_1966_ = lean_ctor_get(v___x_1965_, 9);
v_share_1967_ = lean_ctor_get(v___x_1965_, 0);
v_maxFVar_1968_ = lean_ctor_get(v___x_1965_, 1);
v_proofInstInfo_1969_ = lean_ctor_get(v___x_1965_, 2);
v_inferType_1970_ = lean_ctor_get(v___x_1965_, 3);
v_getLevel_1971_ = lean_ctor_get(v___x_1965_, 4);
v_congrInfo_1972_ = lean_ctor_get(v___x_1965_, 5);
v_defEqI_1973_ = lean_ctor_get(v___x_1965_, 6);
v_extensions_1974_ = lean_ctor_get(v___x_1965_, 7);
v_issues_1975_ = lean_ctor_get(v___x_1965_, 8);
v_instanceOverrides_1976_ = lean_ctor_get(v___x_1965_, 10);
v_debug_1977_ = lean_ctor_get_uint8(v___x_1965_, sizeof(void*)*11);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1979_ = v___x_1965_;
v_isShared_1980_ = v_isSharedCheck_1998_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_instanceOverrides_1976_);
lean_inc(v_canon_1966_);
lean_inc(v_issues_1975_);
lean_inc(v_extensions_1974_);
lean_inc(v_defEqI_1973_);
lean_inc(v_congrInfo_1972_);
lean_inc(v_getLevel_1971_);
lean_inc(v_inferType_1970_);
lean_inc(v_proofInstInfo_1969_);
lean_inc(v_maxFVar_1968_);
lean_inc(v_share_1967_);
lean_dec(v___x_1965_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1998_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_cache_1981_; lean_object* v_cacheInType_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1997_; 
v_cache_1981_ = lean_ctor_get(v_canon_1966_, 0);
v_cacheInType_1982_ = lean_ctor_get(v_canon_1966_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_canon_1966_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1984_ = v_canon_1966_;
v_isShared_1985_ = v_isSharedCheck_1997_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_cacheInType_1982_);
lean_inc(v_cache_1981_);
lean_dec(v_canon_1966_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1997_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_inc(v_a_1961_);
v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1982_, v_e_1916_, v_a_1961_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_cache_1981_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 9, v___x_1988_);
v___x_1990_ = v___x_1979_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_share_1967_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_maxFVar_1968_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_proofInstInfo_1969_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_inferType_1970_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_getLevel_1971_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_congrInfo_1972_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_defEqI_1973_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v_extensions_1974_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v_issues_1975_);
lean_ctor_set(v_reuseFailAlloc_1995_, 9, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 10, v_instanceOverrides_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*11, v_debug_1977_);
v___x_1990_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_st_ref_put(v_a_1919_, v___x_1990_);
if (v_isShared_1964_ == 0)
{
v___x_1993_ = v___x_1963_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1961_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1916_);
return v___y_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2054_, lean_object* v_a_2055_, lean_object* v___x_2056_, lean_object* v_snd_2057_, uint8_t v___x_2058_, lean_object* v_fst_2059_, lean_object* v_____r_2060_, uint8_t v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_arg_x27_2070_; lean_object* v___x_2082_; 
lean_inc_ref(v___x_2056_);
v___x_2082_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2054_, v_a_2055_, v___x_2056_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; uint8_t v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = lean_unbox(v_a_2083_);
lean_dec(v_a_2083_);
switch(v___x_2084_)
{
case 0:
{
lean_object* v___x_2085_; 
lean_inc_ref(v___x_2056_);
v___x_2085_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2056_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v_arg_x27_2070_ = v_a_2086_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2087_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
case 1:
{
lean_object* v___x_2095_; 
lean_inc_ref(v___x_2056_);
v___x_2095_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2056_, v___y_2065_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2115_ = l_Lean_Expr_cleanupAnnotations(v_a_2096_);
v___x_2116_ = l_Lean_Expr_isApp(v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec_ref(v___x_2115_);
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
v___y_2100_ = v___y_2063_;
v___y_2101_ = v___y_2064_;
v___y_2102_ = v___y_2065_;
v___y_2103_ = v___y_2066_;
v___y_2104_ = v___y_2067_;
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_arg_2117_ = lean_ctor_get(v___x_2115_, 1);
lean_inc_ref(v_arg_2117_);
v___x_2118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2115_);
v___x_2119_ = l_Lean_Expr_isApp(v___x_2118_);
if (v___x_2119_ == 0)
{
lean_dec_ref(v___x_2118_);
lean_dec_ref(v_arg_2117_);
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
v___y_2100_ = v___y_2063_;
v___y_2101_ = v___y_2064_;
v___y_2102_ = v___y_2065_;
v___y_2103_ = v___y_2066_;
v___y_2104_ = v___y_2067_;
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v_arg_2120_ = lean_ctor_get(v___x_2118_, 1);
lean_inc_ref(v_arg_2120_);
v___x_2121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2118_);
v___x_2122_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2123_ = l_Lean_Expr_isConstOf(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2125_ = l_Lean_Expr_isConstOf(v___x_2121_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v___x_2121_);
lean_dec_ref(v_arg_2120_);
lean_dec_ref(v_arg_2117_);
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
v___y_2100_ = v___y_2063_;
v___y_2101_ = v___y_2064_;
v___y_2102_ = v___y_2065_;
v___y_2103_ = v___y_2066_;
v___y_2104_ = v___y_2067_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2126_; 
lean_inc_ref(v___x_2056_);
v___x_2126_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2121_, v_arg_2120_, v_arg_2117_, v___x_2056_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_arg_x27_2070_ = v_a_2127_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2128_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2126_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2136_; 
lean_inc_ref(v___x_2056_);
v___x_2136_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2121_, v_arg_2120_, v_arg_2117_, v___x_2056_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v_arg_x27_2070_ = v_a_2137_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2138_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2136_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2136_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
v___jp_2097_:
{
lean_object* v___x_2105_; 
lean_inc_ref(v___x_2056_);
v___x_2105_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2056_, v___x_2058_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v_arg_x27_2070_ = v_a_2106_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2107_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2146_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2095_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2095_);
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
lean_object* v___x_2154_; 
lean_inc_ref(v___x_2056_);
v___x_2154_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2056_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v_arg_x27_2070_ = v_a_2155_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2156_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2154_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2154_);
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
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_fst_2059_);
lean_dec(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2164_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2082_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2082_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
v___jp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; uint8_t v___x_2073_; 
v___x_2071_ = lean_ptr_addr(v___x_2056_);
lean_dec_ref(v___x_2056_);
v___x_2072_ = lean_ptr_addr(v_arg_x27_2070_);
v___x_2073_ = lean_usize_dec_eq(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v_fst_2059_);
v___x_2074_ = lean_array_fset(v_snd_2057_, v_a_2055_, v_arg_x27_2070_);
v___x_2075_ = lean_box(v___x_2058_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v_arg_x27_2070_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v_fst_2059_);
lean_ctor_set(v___x_2079_, 1, v_snd_2057_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2176_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2177_ = l_Lean_Name_append(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2180_ = l_Lean_stringToMessageData(v___x_2179_);
return v___x_2180_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2187_, lean_object* v___x_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_, uint8_t v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___y_2200_; uint8_t v___x_2222_; 
v___x_2222_ = lean_nat_dec_lt(v_a_2189_, v_upperBound_2187_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_a_2189_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2190_);
return v___x_2223_;
}
else
{
lean_object* v_options_2224_; lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2290_; 
v_options_2224_ = lean_ctor_get(v___y_2196_, 2);
v_fst_2225_ = lean_ctor_get(v_b_2190_, 0);
v_snd_2226_ = lean_ctor_get(v_b_2190_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_b_2190_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2228_ = v_b_2190_;
v_isShared_2229_ = v_isSharedCheck_2290_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_snd_2226_);
lean_inc(v_fst_2225_);
lean_dec(v_b_2190_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2290_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_inheritedTraceOptions_2230_; uint8_t v_hasTrace_2231_; lean_object* v___x_2232_; 
v_inheritedTraceOptions_2230_ = lean_ctor_get(v___y_2196_, 13);
v_hasTrace_2231_ = lean_ctor_get_uint8(v_options_2224_, sizeof(void*)*1);
v___x_2232_ = lean_array_fget(v_snd_2226_, v_a_2189_);
if (v_hasTrace_2231_ == 0)
{
lean_del_object(v___x_2228_);
goto v___jp_2233_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2237_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2238_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2230_, v_options_2224_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_del_object(v___x_2228_);
goto v___jp_2233_;
}
else
{
lean_object* v___x_2239_; 
lean_inc(v___x_2232_);
v___x_2239_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2188_, v_a_2189_, v___x_2232_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v___x_2232_);
v___x_2241_ = lean_infer_type(v___x_2232_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; lean_object* v___y_2245_; uint8_t v___x_2269_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2243_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2269_ = lean_unbox(v_a_2240_);
lean_dec(v_a_2240_);
switch(v___x_2269_)
{
case 0:
{
lean_object* v___x_2270_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2245_ = v___x_2270_;
goto v___jp_2244_;
}
case 1:
{
lean_object* v___x_2271_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2245_ = v___x_2271_;
goto v___jp_2244_;
}
case 2:
{
lean_object* v___x_2272_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2245_ = v___x_2272_;
goto v___jp_2244_;
}
default: 
{
lean_object* v___x_2273_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2245_ = v___x_2273_;
goto v___jp_2244_;
}
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_inc(v___y_2245_);
v___x_2246_ = l_Lean_MessageData_ofFormat(v___y_2245_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set_tag(v___x_2228_, 7);
lean_ctor_set(v___x_2228_, 1, v___x_2246_);
lean_ctor_set(v___x_2228_, 0, v___x_2243_);
v___x_2248_ = v___x_2228_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2249_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
lean_inc(v___x_2232_);
v___x_2251_ = l_Lean_MessageData_ofExpr(v___x_2232_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_MessageData_ofExpr(v_a_2242_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2236_, v___x_2256_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2259_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2188_, v_a_2189_, v___x_2232_, v_snd_2226_, v___x_2222_, v_fst_2225_, v_a_2258_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
v___y_2200_ = v___x_2259_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v___x_2232_);
lean_dec(v_snd_2226_);
lean_dec(v_fst_2225_);
lean_dec(v_a_2189_);
v_a_2260_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2257_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2257_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2240_);
lean_dec(v___x_2232_);
lean_del_object(v___x_2228_);
lean_dec(v_snd_2226_);
lean_dec(v_fst_2225_);
lean_dec(v_a_2189_);
v_a_2274_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2241_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2241_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v___x_2232_);
lean_del_object(v___x_2228_);
lean_dec(v_snd_2226_);
lean_dec(v_fst_2225_);
lean_dec(v_a_2189_);
v_a_2282_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2239_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2239_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
v___jp_2233_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_box(0);
v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2188_, v_a_2189_, v___x_2232_, v_snd_2226_, v___x_2222_, v_fst_2225_, v___x_2234_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
v___y_2200_ = v___x_2235_;
goto v___jp_2199_;
}
}
}
v___jp_2199_:
{
if (lean_obj_tag(v___y_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2213_; 
v_a_2201_ = lean_ctor_get(v___y_2200_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___y_2200_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2203_ = v___y_2200_;
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___y_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
if (lean_obj_tag(v_a_2201_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; 
lean_dec(v_a_2189_);
v_a_2205_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v_a_2201_, 1);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_a_2205_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_del_object(v___x_2203_);
v_a_2209_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v_a_2201_, 1);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_add(v_a_2189_, v___x_2210_);
lean_dec(v_a_2189_);
v_a_2189_ = v___x_2211_;
v_b_2190_ = v_a_2209_;
goto _start;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2189_);
v_a_2214_ = lean_ctor_get(v___y_2200_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___y_2200_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___y_2200_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___y_2200_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_, uint8_t v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___y_2304_; uint8_t v_modified_2305_; lean_object* v_f_2306_; uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v_args_2362_; uint8_t v_modified_2363_; uint8_t v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; 
if (lean_obj_tag(v_x_2292_) == 5)
{
lean_object* v_fn_2399_; lean_object* v_arg_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_fn_2399_ = lean_ctor_get(v_x_2292_, 0);
lean_inc_ref(v_fn_2399_);
v_arg_2400_ = lean_ctor_get(v_x_2292_, 1);
lean_inc_ref(v_arg_2400_);
lean_dec_ref_known(v_x_2292_, 2);
v___x_2401_ = lean_array_set(v_x_2293_, v_x_2294_, v_arg_2400_);
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_sub(v_x_2294_, v___x_2402_);
lean_dec(v_x_2294_);
v_x_2292_ = v_fn_2399_;
v_x_2293_ = v___x_2401_;
v_x_2294_ = v___x_2403_;
goto _start;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
lean_dec(v_x_2294_);
v___x_2405_ = lean_array_get_size(v_x_2293_);
v___x_2406_ = lean_unsigned_to_nat(2u);
v___x_2407_ = lean_nat_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
v___y_2378_ = v___y_2295_;
v___y_2379_ = v___y_2296_;
v___y_2380_ = v___y_2297_;
v___y_2381_ = v___y_2298_;
v___y_2382_ = v___y_2299_;
v___y_2383_ = v___y_2300_;
v___y_2384_ = v___y_2301_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2409_ = l_Lean_Expr_isConstOf(v_x_2292_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2411_ = l_Lean_Expr_isConstOf(v_x_2292_, v___x_2410_);
if (v___x_2411_ == 0)
{
v___y_2378_ = v___y_2295_;
v___y_2379_ = v___y_2296_;
v___y_2380_ = v___y_2297_;
v___y_2381_ = v___y_2298_;
v___y_2382_ = v___y_2299_;
v___y_2383_ = v___y_2300_;
v___y_2384_ = v___y_2301_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = l_Lean_instInhabitedExpr;
v___x_2413_ = lean_unsigned_to_nat(0u);
v___x_2414_ = lean_array_get(v___x_2412_, v_x_2293_, v___x_2413_);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_array_get(v___x_2412_, v_x_2293_, v___x_2415_);
lean_dec_ref(v_x_2293_);
v___x_2417_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2292_, v___x_2414_, v___x_2416_, v_e_2291_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2417_;
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_prop_2420_; lean_object* v___x_2421_; 
v___x_2418_ = l_Lean_instInhabitedExpr;
v___x_2419_ = lean_unsigned_to_nat(0u);
v_prop_2420_ = lean_array_get_borrowed(v___x_2418_, v_x_2293_, v___x_2419_);
lean_inc(v_prop_2420_);
v___x_2421_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2420_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2438_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2438_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2438_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
size_t v___x_2426_; size_t v___x_2427_; uint8_t v___x_2428_; 
v___x_2426_ = lean_ptr_addr(v_prop_2420_);
v___x_2427_ = lean_ptr_addr(v_a_2422_);
v___x_2428_ = lean_usize_dec_eq(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_dec_ref(v_e_2291_);
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_array_get(v___x_2418_, v_x_2293_, v___x_2429_);
lean_dec_ref(v_x_2293_);
v___x_2431_ = l_Lean_mkAppB(v_x_2292_, v_a_2422_, v___x_2430_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2431_);
v___x_2433_ = v___x_2424_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v___x_2436_; 
lean_dec(v_a_2422_);
lean_dec_ref(v_x_2293_);
lean_dec_ref(v_x_2292_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_e_2291_);
v___x_2436_ = v___x_2424_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_e_2291_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_dec_ref(v_x_2293_);
lean_dec_ref(v_x_2292_);
lean_dec_ref(v_e_2291_);
return v___x_2421_;
}
}
}
}
v___jp_2303_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_box(0);
lean_inc_ref(v_f_2306_);
v___x_2315_ = l_Lean_Meta_getFunInfo(v_f_2306_, v___x_2314_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_paramInfo_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2351_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_paramInfo_2317_ = lean_ctor_get(v_a_2316_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_a_2316_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_a_2316_, 1);
lean_dec(v_unused_2352_);
v___x_2319_ = v_a_2316_;
v_isShared_2320_ = v_isSharedCheck_2351_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_paramInfo_2317_);
lean_dec(v_a_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2351_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2321_ = lean_array_get_size(v___y_2304_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_box(v_modified_2305_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v___y_2304_);
lean_ctor_set(v___x_2319_, 0, v___x_2323_);
v___x_2325_ = v___x_2319_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___y_2304_);
v___x_2325_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2321_, v_paramInfo_2317_, v___x_2322_, v___x_2325_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec_ref(v_paramInfo_2317_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2341_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_fst_2331_; uint8_t v___x_2332_; 
v_fst_2331_ = lean_ctor_get(v_a_2327_, 0);
v___x_2332_ = lean_unbox(v_fst_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2334_; 
lean_dec(v_a_2327_);
lean_dec_ref(v_f_2306_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v_e_2291_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_e_2291_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v_snd_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_dec_ref(v_e_2291_);
v_snd_2336_ = lean_ctor_get(v_a_2327_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_a_2327_);
v___x_2337_ = l_Lean_mkAppN(v_f_2306_, v_snd_2336_);
lean_dec(v_snd_2336_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2337_);
v___x_2339_ = v___x_2329_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v_f_2306_);
lean_dec_ref(v_e_2291_);
v_a_2342_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2326_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2326_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_f_2306_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_e_2291_);
v_a_2353_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2315_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2315_);
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
v___jp_2361_:
{
lean_object* v___x_2371_; 
lean_inc_ref(v_x_2292_);
v___x_2371_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2292_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; size_t v___x_2373_; size_t v___x_2374_; uint8_t v___x_2375_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_ptr_addr(v_x_2292_);
v___x_2374_ = lean_ptr_addr(v_a_2372_);
v___x_2375_ = lean_usize_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; 
lean_dec_ref(v_x_2292_);
v___x_2376_ = 1;
v___y_2304_ = v_args_2362_;
v_modified_2305_ = v___x_2376_;
v_f_2306_ = v_a_2372_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2365_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2367_;
v___y_2311_ = v___y_2368_;
v___y_2312_ = v___y_2369_;
v___y_2313_ = v___y_2370_;
goto v___jp_2303_;
}
else
{
lean_dec(v_a_2372_);
v___y_2304_ = v_args_2362_;
v_modified_2305_ = v_modified_2363_;
v_f_2306_ = v_x_2292_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2365_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2367_;
v___y_2311_ = v___y_2368_;
v___y_2312_ = v___y_2369_;
v___y_2313_ = v___y_2370_;
goto v___jp_2303_;
}
}
else
{
lean_dec_ref(v_args_2362_);
lean_dec_ref(v_x_2292_);
lean_dec_ref(v_e_2291_);
return v___x_2371_;
}
}
v___jp_2377_:
{
uint8_t v_modified_2385_; lean_object* v___x_2386_; uint8_t v_modified_2387_; 
v_modified_2385_ = 0;
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2387_ = l_Lean_Expr_isConstOf(v_x_2292_, v___x_2386_);
if (v_modified_2387_ == 0)
{
v_args_2362_ = v_x_2293_;
v_modified_2363_ = v_modified_2385_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2382_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2384_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2388_; 
lean_inc_ref(v_x_2293_);
v___x_2388_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2293_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
if (lean_obj_tag(v_a_2389_) == 1)
{
lean_object* v_val_2390_; 
lean_dec_ref(v_x_2293_);
v_val_2390_ = lean_ctor_get(v_a_2389_, 0);
lean_inc(v_val_2390_);
lean_dec_ref_known(v_a_2389_, 1);
v_args_2362_ = v_val_2390_;
v_modified_2363_ = v_modified_2387_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2382_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2384_;
goto v___jp_2361_;
}
else
{
lean_dec(v_a_2389_);
v_args_2362_ = v_x_2293_;
v_modified_2363_ = v_modified_2385_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2382_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2384_;
goto v___jp_2361_;
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_x_2293_);
lean_dec_ref(v_x_2292_);
lean_dec_ref(v_e_2291_);
v_a_2391_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2388_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2388_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2439_, uint8_t v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_dummy_2448_; lean_object* v_nargs_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_dummy_2448_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2449_ = l_Lean_Expr_getAppNumArgs(v_e_2439_);
lean_inc(v_nargs_2449_);
v___x_2450_ = lean_mk_array(v_nargs_2449_, v_dummy_2448_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_sub(v_nargs_2449_, v___x_2451_);
lean_dec(v_nargs_2449_);
lean_inc_ref(v_e_2439_);
v___x_2453_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2439_, v_e_2439_, v___x_2450_, v___x_2452_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2454_, uint8_t v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2464_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2465_;
}
else
{
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2466_, uint8_t v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2466_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
if (lean_obj_tag(v_a_2476_) == 0)
{
lean_object* v_val_2477_; lean_object* v___x_2478_; 
lean_dec_ref(v_e_2466_);
v_val_2477_ = lean_ctor_get(v_a_2476_, 0);
lean_inc_ref(v_val_2477_);
lean_dec_ref_known(v_a_2476_, 1);
v___x_2478_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2477_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
return v___x_2478_;
}
else
{
lean_object* v___x_2479_; 
lean_dec(v_a_2476_);
v___x_2479_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2480_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2491_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2491_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2491_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
if (lean_obj_tag(v_a_2482_) == 0)
{
lean_object* v_val_2486_; lean_object* v___x_2487_; 
lean_del_object(v___x_2484_);
lean_dec(v_a_2480_);
v_val_2486_ = lean_ctor_get(v_a_2482_, 0);
lean_inc_ref(v_val_2486_);
lean_dec_ref_known(v_a_2482_, 1);
v___x_2487_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2486_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
return v___x_2487_;
}
else
{
lean_object* v___x_2489_; 
lean_dec(v_a_2482_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v_a_2480_);
v___x_2489_ = v___x_2484_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2480_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_a_2480_);
v_a_2492_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2481_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2481_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref(v_e_2466_);
v_a_2500_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2475_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2475_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2514_, uint8_t v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2523_; 
lean_inc_ref(v_e_2514_);
v___x_2523_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2514_, v_a_2519_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2535_ = l_Lean_Expr_cleanupAnnotations(v_a_2524_);
v___x_2536_ = l_Lean_Expr_isApp(v___x_2535_);
if (v___x_2536_ == 0)
{
lean_dec_ref(v___x_2535_);
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
v___y_2528_ = v_a_2517_;
v___y_2529_ = v_a_2518_;
v___y_2530_ = v_a_2519_;
v___y_2531_ = v_a_2520_;
v___y_2532_ = v_a_2521_;
goto v___jp_2525_;
}
else
{
lean_object* v_arg_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_arg_2537_ = lean_ctor_get(v___x_2535_, 1);
lean_inc_ref(v_arg_2537_);
v___x_2538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2535_);
v___x_2539_ = l_Lean_Expr_isApp(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec_ref(v___x_2538_);
lean_dec_ref(v_arg_2537_);
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
v___y_2528_ = v_a_2517_;
v___y_2529_ = v_a_2518_;
v___y_2530_ = v_a_2519_;
v___y_2531_ = v_a_2520_;
v___y_2532_ = v_a_2521_;
goto v___jp_2525_;
}
else
{
lean_object* v_arg_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_arg_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc_ref(v_arg_2540_);
v___x_2541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2538_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2543_ = l_Lean_Expr_isConstOf(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_dec_ref(v___x_2541_);
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
v___y_2528_ = v_a_2517_;
v___y_2529_ = v_a_2518_;
v___y_2530_ = v_a_2519_;
v___y_2531_ = v_a_2520_;
v___y_2532_ = v_a_2521_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2541_, v_arg_2540_, v_arg_2537_, v_e_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
return v___x_2544_;
}
}
}
v___jp_2525_:
{
uint8_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = 0;
v___x_2534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2514_, v___x_2533_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2534_;
}
}
else
{
lean_dec_ref(v_e_2514_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2545_, lean_object* v_00_u03b1_2546_, lean_object* v_c_2547_, lean_object* v_inst_2548_, lean_object* v_a_2549_, lean_object* v_b_2550_, uint8_t v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2547_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; uint8_t v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_n(v_a_2560_, 2);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2560_);
if (v___x_2561_ == 0)
{
uint8_t v___x_2562_; 
lean_inc(v_a_2560_);
v___x_2562_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2560_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2546_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2548_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2549_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2578_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2578_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2578_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = l_Lean_mkApp5(v_f_2545_, v_a_2564_, v_a_2560_, v_a_2566_, v_a_2568_, v_a_2570_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_dec(v_a_2568_);
lean_dec(v_a_2566_);
lean_dec(v_a_2564_);
lean_dec(v_a_2560_);
lean_dec_ref(v_f_2545_);
return v___x_2569_;
}
}
else
{
lean_dec(v_a_2566_);
lean_dec(v_a_2564_);
lean_dec(v_a_2560_);
lean_dec_ref(v_b_2550_);
lean_dec_ref(v_f_2545_);
return v___x_2567_;
}
}
else
{
lean_dec(v_a_2564_);
lean_dec(v_a_2560_);
lean_dec_ref(v_b_2550_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_f_2545_);
return v___x_2565_;
}
}
else
{
lean_dec(v_a_2560_);
lean_dec_ref(v_b_2550_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_inst_2548_);
lean_dec_ref(v_f_2545_);
return v___x_2563_;
}
}
else
{
lean_object* v___x_2579_; 
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_inst_2548_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
v___x_2579_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2579_;
}
}
else
{
lean_object* v___x_2580_; 
lean_dec(v_a_2560_);
lean_dec_ref(v_b_2550_);
lean_dec_ref(v_inst_2548_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
v___x_2580_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2549_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2580_;
}
}
else
{
lean_dec_ref(v_b_2550_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_inst_2548_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2581_, lean_object* v_00_u03b1_2582_, lean_object* v_c_2583_, lean_object* v_a_2584_, lean_object* v_b_2585_, uint8_t v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2583_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; uint8_t v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc_n(v_a_2595_, 2);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = l_Lean_Expr_isBoolTrue(v_a_2595_);
if (v___x_2596_ == 0)
{
uint8_t v___x_2597_; 
lean_inc(v_a_2595_);
v___x_2597_ = l_Lean_Expr_isBoolFalse(v_a_2595_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2582_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2584_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = l_Lean_mkApp4(v_f_2581_, v_a_2599_, v_a_2595_, v_a_2601_, v_a_2603_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_dec(v_a_2601_);
lean_dec(v_a_2599_);
lean_dec(v_a_2595_);
lean_dec_ref(v_f_2581_);
return v___x_2602_;
}
}
else
{
lean_dec(v_a_2599_);
lean_dec(v_a_2595_);
lean_dec_ref(v_b_2585_);
lean_dec_ref(v_f_2581_);
return v___x_2600_;
}
}
else
{
lean_dec(v_a_2595_);
lean_dec_ref(v_b_2585_);
lean_dec_ref(v_a_2584_);
lean_dec_ref(v_f_2581_);
return v___x_2598_;
}
}
else
{
lean_object* v___x_2612_; 
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2584_);
lean_dec_ref(v_00_u03b1_2582_);
lean_dec_ref(v_f_2581_);
v___x_2612_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2595_);
lean_dec_ref(v_b_2585_);
lean_dec_ref(v_00_u03b1_2582_);
lean_dec_ref(v_f_2581_);
v___x_2613_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2584_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
return v___x_2613_;
}
}
else
{
lean_dec_ref(v_b_2585_);
lean_dec_ref(v_a_2584_);
lean_dec_ref(v_00_u03b1_2582_);
lean_dec_ref(v_f_2581_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2614_, uint8_t v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
uint8_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; uint8_t v___y_2632_; lean_object* v___x_2650_; 
lean_inc_ref(v_e_2614_);
v___x_2650_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2614_, v_a_2619_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2662_ = l_Lean_Expr_cleanupAnnotations(v_a_2651_);
v___x_2663_ = l_Lean_Expr_isApp(v___x_2662_);
if (v___x_2663_ == 0)
{
lean_dec_ref(v___x_2662_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v_arg_2664_ = lean_ctor_get(v___x_2662_, 1);
lean_inc_ref(v_arg_2664_);
v___x_2665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2662_);
v___x_2666_ = l_Lean_Expr_isApp(v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v___x_2665_);
lean_dec_ref(v_arg_2664_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_arg_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc_ref(v_arg_2667_);
v___x_2668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2665_);
v___x_2669_ = l_Lean_Expr_isApp(v___x_2668_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v___x_2668_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_arg_2670_ = lean_ctor_get(v___x_2668_, 1);
lean_inc_ref(v_arg_2670_);
v___x_2671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2668_);
v___x_2672_ = l_Lean_Expr_isApp(v___x_2671_);
if (v___x_2672_ == 0)
{
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_arg_2673_ = lean_ctor_get(v___x_2671_, 1);
lean_inc_ref(v_arg_2673_);
v___x_2674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2671_);
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2676_ = l_Lean_Expr_isConstOf(v___x_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_Expr_isApp(v___x_2674_);
if (v___x_2677_ == 0)
{
lean_dec_ref(v___x_2674_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_arg_2678_ = lean_ctor_get(v___x_2674_, 1);
lean_inc_ref(v_arg_2678_);
v___x_2679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2674_);
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2681_ = l_Lean_Expr_isConstOf(v___x_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v___x_2679_);
lean_dec_ref(v_arg_2678_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
v___y_2653_ = v_a_2615_;
v___y_2654_ = v_a_2616_;
v___y_2655_ = v_a_2617_;
v___y_2656_ = v_a_2618_;
v___y_2657_ = v_a_2619_;
v___y_2658_ = v_a_2620_;
v___y_2659_ = v_a_2621_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2682_; 
lean_dec_ref(v_e_2614_);
v___x_2682_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2679_, v_arg_2678_, v_arg_2673_, v_arg_2670_, v_arg_2667_, v_arg_2664_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
return v___x_2682_;
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec_ref(v_e_2614_);
v___x_2683_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2674_, v_arg_2673_, v_arg_2670_, v_arg_2667_, v_arg_2664_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
return v___x_2683_;
}
}
}
}
}
v___jp_2652_:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = l_Lean_Expr_getAppFn(v_e_2614_);
v___x_2661_ = l_Lean_Expr_isLambda(v___x_2660_);
if (v___x_2661_ == 0)
{
v___y_2624_ = v___y_2653_;
v___y_2625_ = v___y_2656_;
v___y_2626_ = v___y_2657_;
v___y_2627_ = v___y_2654_;
v___y_2628_ = v___x_2660_;
v___y_2629_ = v___y_2655_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2659_;
v___y_2632_ = v___x_2661_;
goto v___jp_2623_;
}
else
{
v___y_2624_ = v___y_2653_;
v___y_2625_ = v___y_2656_;
v___y_2626_ = v___y_2657_;
v___y_2627_ = v___y_2654_;
v___y_2628_ = v___x_2660_;
v___y_2629_ = v___y_2655_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2659_;
v___y_2632_ = v___y_2653_;
goto v___jp_2623_;
}
}
}
else
{
lean_dec_ref(v_e_2614_);
return v___x_2650_;
}
v___jp_2623_:
{
if (v___y_2632_ == 0)
{
if (lean_obj_tag(v___y_2628_) == 4)
{
lean_object* v_declName_2633_; lean_object* v___x_2634_; 
v_declName_2633_ = lean_ctor_get(v___y_2628_, 0);
lean_inc(v_declName_2633_);
lean_dec_ref_known(v___y_2628_, 2);
v___x_2634_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2633_, v___y_2631_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; uint8_t v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = lean_unbox(v_a_2635_);
lean_dec(v_a_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2614_, v___y_2624_, v___y_2627_, v___y_2629_, v___y_2625_, v___y_2626_, v___y_2630_, v___y_2631_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2614_, v___y_2624_, v___y_2627_, v___y_2629_, v___y_2625_, v___y_2626_, v___y_2630_, v___y_2631_);
return v___x_2638_;
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v_e_2614_);
v_a_2639_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2634_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2634_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v___x_2647_; 
lean_dec_ref(v___y_2628_);
v___x_2647_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2614_, v___y_2624_, v___y_2627_, v___y_2629_, v___y_2625_, v___y_2626_, v___y_2630_, v___y_2631_);
return v___x_2647_;
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec_ref(v___y_2628_);
v___x_2648_ = l_Lean_Expr_headBeta(v_e_2614_);
v___x_2649_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2648_, v___y_2624_, v___y_2627_, v___y_2629_, v___y_2625_, v___y_2626_, v___y_2630_, v___y_2631_);
return v___x_2649_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2688_ = lean_unsigned_to_nat(18u);
v___x_2689_ = lean_unsigned_to_nat(1896u);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2692_ = l_mkPanicMessageWithDecl(v___x_2691_, v___x_2690_, v___x_2689_, v___x_2688_, v___x_2687_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2693_, uint8_t v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = l_Lean_Expr_projExpr_x21(v_e_2693_);
v___x_2703_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2702_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___y_2706_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
if (lean_obj_tag(v_e_2693_) == 11)
{
lean_object* v_typeName_2728_; lean_object* v_idx_2729_; lean_object* v_struct_2730_; size_t v___x_2731_; size_t v___x_2732_; uint8_t v___x_2733_; 
v_typeName_2728_ = lean_ctor_get(v_e_2693_, 0);
v_idx_2729_ = lean_ctor_get(v_e_2693_, 1);
v_struct_2730_ = lean_ctor_get(v_e_2693_, 2);
v___x_2731_ = lean_ptr_addr(v_struct_2730_);
v___x_2732_ = lean_ptr_addr(v_a_2704_);
v___x_2733_ = lean_usize_dec_eq(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
lean_inc(v_idx_2729_);
lean_inc(v_typeName_2728_);
lean_dec_ref_known(v_e_2693_, 3);
v___x_2734_ = l_Lean_Expr_proj___override(v_typeName_2728_, v_idx_2729_, v_a_2704_);
v___y_2706_ = v___x_2734_;
goto v___jp_2705_;
}
else
{
lean_dec(v_a_2704_);
v___y_2706_ = v_e_2693_;
goto v___jp_2705_;
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v_a_2704_);
lean_dec_ref(v_e_2693_);
v___x_2735_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2736_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2735_);
v___y_2706_ = v___x_2736_;
goto v___jp_2705_;
}
v___jp_2705_:
{
lean_object* v___x_2707_; 
lean_inc_ref(v___y_2706_);
v___x_2707_ = l_Lean_Meta_reduceProj_x3f(v___y_2706_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2719_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
if (lean_obj_tag(v_a_2708_) == 0)
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___y_2706_);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___y_2706_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2717_; 
lean_dec_ref(v___y_2706_);
v_val_2715_ = lean_ctor_get(v_a_2708_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v_a_2708_, 1);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v_val_2715_);
v___x_2717_ = v___x_2710_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_val_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___y_2706_);
v_a_2720_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2707_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2707_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2693_);
return v___x_2703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2737_, uint8_t v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
switch(lean_obj_tag(v_e_2737_))
{
case 7:
{
lean_object* v___x_2746_; 
v___x_2746_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2738_ == 0)
{
lean_object* v___x_2747_; lean_object* v_canon_2748_; lean_object* v_cache_2749_; lean_object* v___x_2750_; 
v___x_2747_ = lean_st_ref_get(v_a_2740_);
v_canon_2748_ = lean_ctor_get(v___x_2747_, 9);
lean_inc_ref(v_canon_2748_);
lean_dec(v___x_2747_);
v_cache_2749_ = lean_ctor_get(v_canon_2748_, 0);
lean_inc_ref(v_cache_2749_);
lean_dec_ref(v_canon_2748_);
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2749_, v_e_2737_);
lean_dec_ref(v_cache_2749_);
if (lean_obj_tag(v___x_2750_) == 1)
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 0);
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_val_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v___x_2759_; 
lean_dec(v___x_2750_);
lean_inc_ref(v_e_2737_);
v___x_2759_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2746_, v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2798_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2798_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2798_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v_canon_2765_; lean_object* v_share_2766_; lean_object* v_maxFVar_2767_; lean_object* v_proofInstInfo_2768_; lean_object* v_inferType_2769_; lean_object* v_getLevel_2770_; lean_object* v_congrInfo_2771_; lean_object* v_defEqI_2772_; lean_object* v_extensions_2773_; lean_object* v_issues_2774_; lean_object* v_instanceOverrides_2775_; uint8_t v_debug_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2797_; 
v___x_2764_ = lean_st_ref_take(v_a_2740_);
v_canon_2765_ = lean_ctor_get(v___x_2764_, 9);
v_share_2766_ = lean_ctor_get(v___x_2764_, 0);
v_maxFVar_2767_ = lean_ctor_get(v___x_2764_, 1);
v_proofInstInfo_2768_ = lean_ctor_get(v___x_2764_, 2);
v_inferType_2769_ = lean_ctor_get(v___x_2764_, 3);
v_getLevel_2770_ = lean_ctor_get(v___x_2764_, 4);
v_congrInfo_2771_ = lean_ctor_get(v___x_2764_, 5);
v_defEqI_2772_ = lean_ctor_get(v___x_2764_, 6);
v_extensions_2773_ = lean_ctor_get(v___x_2764_, 7);
v_issues_2774_ = lean_ctor_get(v___x_2764_, 8);
v_instanceOverrides_2775_ = lean_ctor_get(v___x_2764_, 10);
v_debug_2776_ = lean_ctor_get_uint8(v___x_2764_, sizeof(void*)*11);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2778_ = v___x_2764_;
v_isShared_2779_ = v_isSharedCheck_2797_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_instanceOverrides_2775_);
lean_inc(v_canon_2765_);
lean_inc(v_issues_2774_);
lean_inc(v_extensions_2773_);
lean_inc(v_defEqI_2772_);
lean_inc(v_congrInfo_2771_);
lean_inc(v_getLevel_2770_);
lean_inc(v_inferType_2769_);
lean_inc(v_proofInstInfo_2768_);
lean_inc(v_maxFVar_2767_);
lean_inc(v_share_2766_);
lean_dec(v___x_2764_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2797_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_cache_2780_; lean_object* v_cacheInType_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2796_; 
v_cache_2780_ = lean_ctor_get(v_canon_2765_, 0);
v_cacheInType_2781_ = lean_ctor_get(v_canon_2765_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_canon_2765_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2783_ = v_canon_2765_;
v_isShared_2784_ = v_isSharedCheck_2796_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_cacheInType_2781_);
lean_inc(v_cache_2780_);
lean_dec(v_canon_2765_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2796_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_inc(v_a_2760_);
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2780_, v_e_2737_, v_a_2760_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_cacheInType_2781_);
v___x_2787_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 9, v___x_2787_);
v___x_2789_ = v___x_2778_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_share_2766_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_maxFVar_2767_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_proofInstInfo_2768_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_inferType_2769_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_getLevel_2770_);
lean_ctor_set(v_reuseFailAlloc_2794_, 5, v_congrInfo_2771_);
lean_ctor_set(v_reuseFailAlloc_2794_, 6, v_defEqI_2772_);
lean_ctor_set(v_reuseFailAlloc_2794_, 7, v_extensions_2773_);
lean_ctor_set(v_reuseFailAlloc_2794_, 8, v_issues_2774_);
lean_ctor_set(v_reuseFailAlloc_2794_, 9, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2794_, 10, v_instanceOverrides_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, sizeof(void*)*11, v_debug_2776_);
v___x_2789_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_st_ref_put(v_a_2740_, v___x_2789_);
if (v_isShared_2763_ == 0)
{
v___x_2792_ = v___x_2762_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2760_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_2759_;
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v_canon_2800_; lean_object* v_cacheInType_2801_; lean_object* v___x_2802_; 
v___x_2799_ = lean_st_ref_get(v_a_2740_);
v_canon_2800_ = lean_ctor_get(v___x_2799_, 9);
lean_inc_ref(v_canon_2800_);
lean_dec(v___x_2799_);
v_cacheInType_2801_ = lean_ctor_get(v_canon_2800_, 1);
lean_inc_ref(v_cacheInType_2801_);
lean_dec_ref(v_canon_2800_);
v___x_2802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2801_, v_e_2737_);
lean_dec_ref(v_cacheInType_2801_);
if (lean_obj_tag(v___x_2802_) == 1)
{
lean_object* v_val_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_val_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_val_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v___x_2811_; 
lean_dec(v___x_2802_);
lean_inc_ref(v_e_2737_);
v___x_2811_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2746_, v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2850_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2850_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2850_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v_canon_2817_; lean_object* v_share_2818_; lean_object* v_maxFVar_2819_; lean_object* v_proofInstInfo_2820_; lean_object* v_inferType_2821_; lean_object* v_getLevel_2822_; lean_object* v_congrInfo_2823_; lean_object* v_defEqI_2824_; lean_object* v_extensions_2825_; lean_object* v_issues_2826_; lean_object* v_instanceOverrides_2827_; uint8_t v_debug_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2849_; 
v___x_2816_ = lean_st_ref_take(v_a_2740_);
v_canon_2817_ = lean_ctor_get(v___x_2816_, 9);
v_share_2818_ = lean_ctor_get(v___x_2816_, 0);
v_maxFVar_2819_ = lean_ctor_get(v___x_2816_, 1);
v_proofInstInfo_2820_ = lean_ctor_get(v___x_2816_, 2);
v_inferType_2821_ = lean_ctor_get(v___x_2816_, 3);
v_getLevel_2822_ = lean_ctor_get(v___x_2816_, 4);
v_congrInfo_2823_ = lean_ctor_get(v___x_2816_, 5);
v_defEqI_2824_ = lean_ctor_get(v___x_2816_, 6);
v_extensions_2825_ = lean_ctor_get(v___x_2816_, 7);
v_issues_2826_ = lean_ctor_get(v___x_2816_, 8);
v_instanceOverrides_2827_ = lean_ctor_get(v___x_2816_, 10);
v_debug_2828_ = lean_ctor_get_uint8(v___x_2816_, sizeof(void*)*11);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2830_ = v___x_2816_;
v_isShared_2831_ = v_isSharedCheck_2849_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_instanceOverrides_2827_);
lean_inc(v_canon_2817_);
lean_inc(v_issues_2826_);
lean_inc(v_extensions_2825_);
lean_inc(v_defEqI_2824_);
lean_inc(v_congrInfo_2823_);
lean_inc(v_getLevel_2822_);
lean_inc(v_inferType_2821_);
lean_inc(v_proofInstInfo_2820_);
lean_inc(v_maxFVar_2819_);
lean_inc(v_share_2818_);
lean_dec(v___x_2816_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2849_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_cache_2832_; lean_object* v_cacheInType_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2848_; 
v_cache_2832_ = lean_ctor_get(v_canon_2817_, 0);
v_cacheInType_2833_ = lean_ctor_get(v_canon_2817_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_canon_2817_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2835_ = v_canon_2817_;
v_isShared_2836_ = v_isSharedCheck_2848_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_cacheInType_2833_);
lean_inc(v_cache_2832_);
lean_dec(v_canon_2817_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2848_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_inc(v_a_2812_);
v___x_2837_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2833_, v_e_2737_, v_a_2812_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_cache_2832_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 9, v___x_2839_);
v___x_2841_ = v___x_2830_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_share_2818_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_maxFVar_2819_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_proofInstInfo_2820_);
lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_inferType_2821_);
lean_ctor_set(v_reuseFailAlloc_2846_, 4, v_getLevel_2822_);
lean_ctor_set(v_reuseFailAlloc_2846_, 5, v_congrInfo_2823_);
lean_ctor_set(v_reuseFailAlloc_2846_, 6, v_defEqI_2824_);
lean_ctor_set(v_reuseFailAlloc_2846_, 7, v_extensions_2825_);
lean_ctor_set(v_reuseFailAlloc_2846_, 8, v_issues_2826_);
lean_ctor_set(v_reuseFailAlloc_2846_, 9, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2846_, 10, v_instanceOverrides_2827_);
lean_ctor_set_uint8(v_reuseFailAlloc_2846_, sizeof(void*)*11, v_debug_2828_);
v___x_2841_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_st_ref_put(v_a_2740_, v___x_2841_);
if (v_isShared_2815_ == 0)
{
v___x_2844_ = v___x_2814_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2812_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_2811_;
}
}
}
}
case 6:
{
if (v_a_2738_ == 0)
{
lean_object* v___x_2851_; lean_object* v_canon_2852_; lean_object* v_cache_2853_; lean_object* v___x_2854_; 
v___x_2851_ = lean_st_ref_get(v_a_2740_);
v_canon_2852_ = lean_ctor_get(v___x_2851_, 9);
lean_inc_ref(v_canon_2852_);
lean_dec(v___x_2851_);
v_cache_2853_ = lean_ctor_get(v_canon_2852_, 0);
lean_inc_ref(v_cache_2853_);
lean_dec_ref(v_canon_2852_);
v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2853_, v_e_2737_);
lean_dec_ref(v_cache_2853_);
if (lean_obj_tag(v___x_2854_) == 1)
{
lean_object* v_val_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_val_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 0);
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_val_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
else
{
lean_object* v___x_2863_; 
lean_dec(v___x_2854_);
lean_inc_ref(v_e_2737_);
v___x_2863_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2902_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2902_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2902_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v_canon_2869_; lean_object* v_share_2870_; lean_object* v_maxFVar_2871_; lean_object* v_proofInstInfo_2872_; lean_object* v_inferType_2873_; lean_object* v_getLevel_2874_; lean_object* v_congrInfo_2875_; lean_object* v_defEqI_2876_; lean_object* v_extensions_2877_; lean_object* v_issues_2878_; lean_object* v_instanceOverrides_2879_; uint8_t v_debug_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2901_; 
v___x_2868_ = lean_st_ref_take(v_a_2740_);
v_canon_2869_ = lean_ctor_get(v___x_2868_, 9);
v_share_2870_ = lean_ctor_get(v___x_2868_, 0);
v_maxFVar_2871_ = lean_ctor_get(v___x_2868_, 1);
v_proofInstInfo_2872_ = lean_ctor_get(v___x_2868_, 2);
v_inferType_2873_ = lean_ctor_get(v___x_2868_, 3);
v_getLevel_2874_ = lean_ctor_get(v___x_2868_, 4);
v_congrInfo_2875_ = lean_ctor_get(v___x_2868_, 5);
v_defEqI_2876_ = lean_ctor_get(v___x_2868_, 6);
v_extensions_2877_ = lean_ctor_get(v___x_2868_, 7);
v_issues_2878_ = lean_ctor_get(v___x_2868_, 8);
v_instanceOverrides_2879_ = lean_ctor_get(v___x_2868_, 10);
v_debug_2880_ = lean_ctor_get_uint8(v___x_2868_, sizeof(void*)*11);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2882_ = v___x_2868_;
v_isShared_2883_ = v_isSharedCheck_2901_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_instanceOverrides_2879_);
lean_inc(v_canon_2869_);
lean_inc(v_issues_2878_);
lean_inc(v_extensions_2877_);
lean_inc(v_defEqI_2876_);
lean_inc(v_congrInfo_2875_);
lean_inc(v_getLevel_2874_);
lean_inc(v_inferType_2873_);
lean_inc(v_proofInstInfo_2872_);
lean_inc(v_maxFVar_2871_);
lean_inc(v_share_2870_);
lean_dec(v___x_2868_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2901_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_cache_2884_; lean_object* v_cacheInType_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2900_; 
v_cache_2884_ = lean_ctor_get(v_canon_2869_, 0);
v_cacheInType_2885_ = lean_ctor_get(v_canon_2869_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_canon_2869_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2887_ = v_canon_2869_;
v_isShared_2888_ = v_isSharedCheck_2900_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_cacheInType_2885_);
lean_inc(v_cache_2884_);
lean_dec(v_canon_2869_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2900_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_inc(v_a_2864_);
v___x_2889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2884_, v_e_2737_, v_a_2864_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_cacheInType_2885_);
v___x_2891_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2893_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 9, v___x_2891_);
v___x_2893_ = v___x_2882_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_share_2870_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_maxFVar_2871_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_proofInstInfo_2872_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_inferType_2873_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_getLevel_2874_);
lean_ctor_set(v_reuseFailAlloc_2898_, 5, v_congrInfo_2875_);
lean_ctor_set(v_reuseFailAlloc_2898_, 6, v_defEqI_2876_);
lean_ctor_set(v_reuseFailAlloc_2898_, 7, v_extensions_2877_);
lean_ctor_set(v_reuseFailAlloc_2898_, 8, v_issues_2878_);
lean_ctor_set(v_reuseFailAlloc_2898_, 9, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 10, v_instanceOverrides_2879_);
lean_ctor_set_uint8(v_reuseFailAlloc_2898_, sizeof(void*)*11, v_debug_2880_);
v___x_2893_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_st_ref_put(v_a_2740_, v___x_2893_);
if (v_isShared_2867_ == 0)
{
v___x_2896_ = v___x_2866_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2864_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_2863_;
}
}
}
else
{
lean_object* v___x_2903_; lean_object* v_canon_2904_; lean_object* v_cacheInType_2905_; lean_object* v___x_2906_; 
v___x_2903_ = lean_st_ref_get(v_a_2740_);
v_canon_2904_ = lean_ctor_get(v___x_2903_, 9);
lean_inc_ref(v_canon_2904_);
lean_dec(v___x_2903_);
v_cacheInType_2905_ = lean_ctor_get(v_canon_2904_, 1);
lean_inc_ref(v_cacheInType_2905_);
lean_dec_ref(v_canon_2904_);
v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2905_, v_e_2737_);
lean_dec_ref(v_cacheInType_2905_);
if (lean_obj_tag(v___x_2906_) == 1)
{
lean_object* v_val_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_val_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set_tag(v___x_2909_, 0);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_val_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v___x_2915_; 
lean_dec(v___x_2906_);
lean_inc_ref(v_e_2737_);
v___x_2915_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2954_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2954_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2954_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v_canon_2921_; lean_object* v_share_2922_; lean_object* v_maxFVar_2923_; lean_object* v_proofInstInfo_2924_; lean_object* v_inferType_2925_; lean_object* v_getLevel_2926_; lean_object* v_congrInfo_2927_; lean_object* v_defEqI_2928_; lean_object* v_extensions_2929_; lean_object* v_issues_2930_; lean_object* v_instanceOverrides_2931_; uint8_t v_debug_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2953_; 
v___x_2920_ = lean_st_ref_take(v_a_2740_);
v_canon_2921_ = lean_ctor_get(v___x_2920_, 9);
v_share_2922_ = lean_ctor_get(v___x_2920_, 0);
v_maxFVar_2923_ = lean_ctor_get(v___x_2920_, 1);
v_proofInstInfo_2924_ = lean_ctor_get(v___x_2920_, 2);
v_inferType_2925_ = lean_ctor_get(v___x_2920_, 3);
v_getLevel_2926_ = lean_ctor_get(v___x_2920_, 4);
v_congrInfo_2927_ = lean_ctor_get(v___x_2920_, 5);
v_defEqI_2928_ = lean_ctor_get(v___x_2920_, 6);
v_extensions_2929_ = lean_ctor_get(v___x_2920_, 7);
v_issues_2930_ = lean_ctor_get(v___x_2920_, 8);
v_instanceOverrides_2931_ = lean_ctor_get(v___x_2920_, 10);
v_debug_2932_ = lean_ctor_get_uint8(v___x_2920_, sizeof(void*)*11);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2934_ = v___x_2920_;
v_isShared_2935_ = v_isSharedCheck_2953_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_instanceOverrides_2931_);
lean_inc(v_canon_2921_);
lean_inc(v_issues_2930_);
lean_inc(v_extensions_2929_);
lean_inc(v_defEqI_2928_);
lean_inc(v_congrInfo_2927_);
lean_inc(v_getLevel_2926_);
lean_inc(v_inferType_2925_);
lean_inc(v_proofInstInfo_2924_);
lean_inc(v_maxFVar_2923_);
lean_inc(v_share_2922_);
lean_dec(v___x_2920_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2953_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v_cache_2936_; lean_object* v_cacheInType_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2952_; 
v_cache_2936_ = lean_ctor_get(v_canon_2921_, 0);
v_cacheInType_2937_ = lean_ctor_get(v_canon_2921_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_canon_2921_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2939_ = v_canon_2921_;
v_isShared_2940_ = v_isSharedCheck_2952_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_cacheInType_2937_);
lean_inc(v_cache_2936_);
lean_dec(v_canon_2921_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2952_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_inc(v_a_2916_);
v___x_2941_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2937_, v_e_2737_, v_a_2916_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_cache_2936_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 9, v___x_2943_);
v___x_2945_ = v___x_2934_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_share_2922_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_maxFVar_2923_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_proofInstInfo_2924_);
lean_ctor_set(v_reuseFailAlloc_2950_, 3, v_inferType_2925_);
lean_ctor_set(v_reuseFailAlloc_2950_, 4, v_getLevel_2926_);
lean_ctor_set(v_reuseFailAlloc_2950_, 5, v_congrInfo_2927_);
lean_ctor_set(v_reuseFailAlloc_2950_, 6, v_defEqI_2928_);
lean_ctor_set(v_reuseFailAlloc_2950_, 7, v_extensions_2929_);
lean_ctor_set(v_reuseFailAlloc_2950_, 8, v_issues_2930_);
lean_ctor_set(v_reuseFailAlloc_2950_, 9, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2950_, 10, v_instanceOverrides_2931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2950_, sizeof(void*)*11, v_debug_2932_);
v___x_2945_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_st_ref_put(v_a_2740_, v___x_2945_);
if (v_isShared_2919_ == 0)
{
v___x_2948_ = v___x_2918_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2916_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_2915_;
}
}
}
}
case 8:
{
lean_object* v___x_2955_; 
v___x_2955_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2738_ == 0)
{
lean_object* v___x_2956_; lean_object* v_canon_2957_; lean_object* v_cache_2958_; lean_object* v___x_2959_; 
v___x_2956_ = lean_st_ref_get(v_a_2740_);
v_canon_2957_ = lean_ctor_get(v___x_2956_, 9);
lean_inc_ref(v_canon_2957_);
lean_dec(v___x_2956_);
v_cache_2958_ = lean_ctor_get(v_canon_2957_, 0);
lean_inc_ref(v_cache_2958_);
lean_dec_ref(v_canon_2957_);
v___x_2959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2958_, v_e_2737_);
lean_dec_ref(v_cache_2958_);
if (lean_obj_tag(v___x_2959_) == 1)
{
lean_object* v_val_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref_known(v_e_2737_, 4);
v_val_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_val_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 0);
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_val_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v___x_2959_);
lean_inc_ref(v_e_2737_);
v___x_2968_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2955_, v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3007_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_3007_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3007_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v_canon_2974_; lean_object* v_share_2975_; lean_object* v_maxFVar_2976_; lean_object* v_proofInstInfo_2977_; lean_object* v_inferType_2978_; lean_object* v_getLevel_2979_; lean_object* v_congrInfo_2980_; lean_object* v_defEqI_2981_; lean_object* v_extensions_2982_; lean_object* v_issues_2983_; lean_object* v_instanceOverrides_2984_; uint8_t v_debug_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3006_; 
v___x_2973_ = lean_st_ref_take(v_a_2740_);
v_canon_2974_ = lean_ctor_get(v___x_2973_, 9);
v_share_2975_ = lean_ctor_get(v___x_2973_, 0);
v_maxFVar_2976_ = lean_ctor_get(v___x_2973_, 1);
v_proofInstInfo_2977_ = lean_ctor_get(v___x_2973_, 2);
v_inferType_2978_ = lean_ctor_get(v___x_2973_, 3);
v_getLevel_2979_ = lean_ctor_get(v___x_2973_, 4);
v_congrInfo_2980_ = lean_ctor_get(v___x_2973_, 5);
v_defEqI_2981_ = lean_ctor_get(v___x_2973_, 6);
v_extensions_2982_ = lean_ctor_get(v___x_2973_, 7);
v_issues_2983_ = lean_ctor_get(v___x_2973_, 8);
v_instanceOverrides_2984_ = lean_ctor_get(v___x_2973_, 10);
v_debug_2985_ = lean_ctor_get_uint8(v___x_2973_, sizeof(void*)*11);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2987_ = v___x_2973_;
v_isShared_2988_ = v_isSharedCheck_3006_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_instanceOverrides_2984_);
lean_inc(v_canon_2974_);
lean_inc(v_issues_2983_);
lean_inc(v_extensions_2982_);
lean_inc(v_defEqI_2981_);
lean_inc(v_congrInfo_2980_);
lean_inc(v_getLevel_2979_);
lean_inc(v_inferType_2978_);
lean_inc(v_proofInstInfo_2977_);
lean_inc(v_maxFVar_2976_);
lean_inc(v_share_2975_);
lean_dec(v___x_2973_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3006_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_cache_2989_; lean_object* v_cacheInType_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3005_; 
v_cache_2989_ = lean_ctor_get(v_canon_2974_, 0);
v_cacheInType_2990_ = lean_ctor_get(v_canon_2974_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_canon_2974_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2992_ = v_canon_2974_;
v_isShared_2993_ = v_isSharedCheck_3005_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_cacheInType_2990_);
lean_inc(v_cache_2989_);
lean_dec(v_canon_2974_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3005_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
lean_inc(v_a_2969_);
v___x_2994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2989_, v_e_2737_, v_a_2969_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_cacheInType_2990_);
v___x_2996_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 9, v___x_2996_);
v___x_2998_ = v___x_2987_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_share_2975_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_maxFVar_2976_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_proofInstInfo_2977_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_inferType_2978_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_getLevel_2979_);
lean_ctor_set(v_reuseFailAlloc_3003_, 5, v_congrInfo_2980_);
lean_ctor_set(v_reuseFailAlloc_3003_, 6, v_defEqI_2981_);
lean_ctor_set(v_reuseFailAlloc_3003_, 7, v_extensions_2982_);
lean_ctor_set(v_reuseFailAlloc_3003_, 8, v_issues_2983_);
lean_ctor_set(v_reuseFailAlloc_3003_, 9, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3003_, 10, v_instanceOverrides_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*11, v_debug_2985_);
v___x_2998_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = lean_st_ref_put(v_a_2740_, v___x_2998_);
if (v_isShared_2972_ == 0)
{
v___x_3001_ = v___x_2971_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2969_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 4);
return v___x_2968_;
}
}
}
else
{
lean_object* v___x_3008_; lean_object* v_canon_3009_; lean_object* v_cacheInType_3010_; lean_object* v___x_3011_; 
v___x_3008_ = lean_st_ref_get(v_a_2740_);
v_canon_3009_ = lean_ctor_get(v___x_3008_, 9);
lean_inc_ref(v_canon_3009_);
lean_dec(v___x_3008_);
v_cacheInType_3010_ = lean_ctor_get(v_canon_3009_, 1);
lean_inc_ref(v_cacheInType_3010_);
lean_dec_ref(v_canon_3009_);
v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3010_, v_e_2737_);
lean_dec_ref(v_cacheInType_3010_);
if (lean_obj_tag(v___x_3011_) == 1)
{
lean_object* v_val_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref_known(v_e_2737_, 4);
v_val_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_val_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 0);
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_val_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___x_3011_);
lean_inc_ref(v_e_2737_);
v___x_3020_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2955_, v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3059_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3059_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3059_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v_canon_3026_; lean_object* v_share_3027_; lean_object* v_maxFVar_3028_; lean_object* v_proofInstInfo_3029_; lean_object* v_inferType_3030_; lean_object* v_getLevel_3031_; lean_object* v_congrInfo_3032_; lean_object* v_defEqI_3033_; lean_object* v_extensions_3034_; lean_object* v_issues_3035_; lean_object* v_instanceOverrides_3036_; uint8_t v_debug_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3058_; 
v___x_3025_ = lean_st_ref_take(v_a_2740_);
v_canon_3026_ = lean_ctor_get(v___x_3025_, 9);
v_share_3027_ = lean_ctor_get(v___x_3025_, 0);
v_maxFVar_3028_ = lean_ctor_get(v___x_3025_, 1);
v_proofInstInfo_3029_ = lean_ctor_get(v___x_3025_, 2);
v_inferType_3030_ = lean_ctor_get(v___x_3025_, 3);
v_getLevel_3031_ = lean_ctor_get(v___x_3025_, 4);
v_congrInfo_3032_ = lean_ctor_get(v___x_3025_, 5);
v_defEqI_3033_ = lean_ctor_get(v___x_3025_, 6);
v_extensions_3034_ = lean_ctor_get(v___x_3025_, 7);
v_issues_3035_ = lean_ctor_get(v___x_3025_, 8);
v_instanceOverrides_3036_ = lean_ctor_get(v___x_3025_, 10);
v_debug_3037_ = lean_ctor_get_uint8(v___x_3025_, sizeof(void*)*11);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3039_ = v___x_3025_;
v_isShared_3040_ = v_isSharedCheck_3058_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_instanceOverrides_3036_);
lean_inc(v_canon_3026_);
lean_inc(v_issues_3035_);
lean_inc(v_extensions_3034_);
lean_inc(v_defEqI_3033_);
lean_inc(v_congrInfo_3032_);
lean_inc(v_getLevel_3031_);
lean_inc(v_inferType_3030_);
lean_inc(v_proofInstInfo_3029_);
lean_inc(v_maxFVar_3028_);
lean_inc(v_share_3027_);
lean_dec(v___x_3025_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3058_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_cache_3041_; lean_object* v_cacheInType_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3057_; 
v_cache_3041_ = lean_ctor_get(v_canon_3026_, 0);
v_cacheInType_3042_ = lean_ctor_get(v_canon_3026_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_canon_3026_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3044_ = v_canon_3026_;
v_isShared_3045_ = v_isSharedCheck_3057_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_cacheInType_3042_);
lean_inc(v_cache_3041_);
lean_dec(v_canon_3026_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3057_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_inc(v_a_3021_);
v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3042_, v_e_2737_, v_a_3021_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_cache_3041_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 9, v___x_3048_);
v___x_3050_ = v___x_3039_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_share_3027_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_maxFVar_3028_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_proofInstInfo_3029_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_inferType_3030_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_getLevel_3031_);
lean_ctor_set(v_reuseFailAlloc_3055_, 5, v_congrInfo_3032_);
lean_ctor_set(v_reuseFailAlloc_3055_, 6, v_defEqI_3033_);
lean_ctor_set(v_reuseFailAlloc_3055_, 7, v_extensions_3034_);
lean_ctor_set(v_reuseFailAlloc_3055_, 8, v_issues_3035_);
lean_ctor_set(v_reuseFailAlloc_3055_, 9, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3055_, 10, v_instanceOverrides_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*11, v_debug_3037_);
v___x_3050_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = lean_st_ref_put(v_a_2740_, v___x_3050_);
if (v_isShared_3024_ == 0)
{
v___x_3053_ = v___x_3023_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3021_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 4);
return v___x_3020_;
}
}
}
}
case 5:
{
if (v_a_2738_ == 0)
{
lean_object* v___x_3060_; lean_object* v_canon_3061_; lean_object* v_cache_3062_; lean_object* v___x_3063_; 
v___x_3060_ = lean_st_ref_get(v_a_2740_);
v_canon_3061_ = lean_ctor_get(v___x_3060_, 9);
lean_inc_ref(v_canon_3061_);
lean_dec(v___x_3060_);
v_cache_3062_ = lean_ctor_get(v_canon_3061_, 0);
lean_inc_ref(v_cache_3062_);
lean_dec_ref(v_canon_3061_);
v___x_3063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3062_, v_e_2737_);
lean_dec_ref(v_cache_3062_);
if (lean_obj_tag(v___x_3063_) == 1)
{
lean_object* v_val_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref_known(v_e_2737_, 2);
v_val_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_val_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 0);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_val_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_object* v___x_3072_; 
lean_dec(v___x_3063_);
lean_inc_ref(v_e_2737_);
v___x_3072_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3111_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3111_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3111_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v_canon_3078_; lean_object* v_share_3079_; lean_object* v_maxFVar_3080_; lean_object* v_proofInstInfo_3081_; lean_object* v_inferType_3082_; lean_object* v_getLevel_3083_; lean_object* v_congrInfo_3084_; lean_object* v_defEqI_3085_; lean_object* v_extensions_3086_; lean_object* v_issues_3087_; lean_object* v_instanceOverrides_3088_; uint8_t v_debug_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3110_; 
v___x_3077_ = lean_st_ref_take(v_a_2740_);
v_canon_3078_ = lean_ctor_get(v___x_3077_, 9);
v_share_3079_ = lean_ctor_get(v___x_3077_, 0);
v_maxFVar_3080_ = lean_ctor_get(v___x_3077_, 1);
v_proofInstInfo_3081_ = lean_ctor_get(v___x_3077_, 2);
v_inferType_3082_ = lean_ctor_get(v___x_3077_, 3);
v_getLevel_3083_ = lean_ctor_get(v___x_3077_, 4);
v_congrInfo_3084_ = lean_ctor_get(v___x_3077_, 5);
v_defEqI_3085_ = lean_ctor_get(v___x_3077_, 6);
v_extensions_3086_ = lean_ctor_get(v___x_3077_, 7);
v_issues_3087_ = lean_ctor_get(v___x_3077_, 8);
v_instanceOverrides_3088_ = lean_ctor_get(v___x_3077_, 10);
v_debug_3089_ = lean_ctor_get_uint8(v___x_3077_, sizeof(void*)*11);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3091_ = v___x_3077_;
v_isShared_3092_ = v_isSharedCheck_3110_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_instanceOverrides_3088_);
lean_inc(v_canon_3078_);
lean_inc(v_issues_3087_);
lean_inc(v_extensions_3086_);
lean_inc(v_defEqI_3085_);
lean_inc(v_congrInfo_3084_);
lean_inc(v_getLevel_3083_);
lean_inc(v_inferType_3082_);
lean_inc(v_proofInstInfo_3081_);
lean_inc(v_maxFVar_3080_);
lean_inc(v_share_3079_);
lean_dec(v___x_3077_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3110_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_cache_3093_; lean_object* v_cacheInType_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3109_; 
v_cache_3093_ = lean_ctor_get(v_canon_3078_, 0);
v_cacheInType_3094_ = lean_ctor_get(v_canon_3078_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_canon_3078_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3096_ = v_canon_3078_;
v_isShared_3097_ = v_isSharedCheck_3109_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_cacheInType_3094_);
lean_inc(v_cache_3093_);
lean_dec(v_canon_3078_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3109_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
lean_inc(v_a_3073_);
v___x_3098_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3093_, v_e_2737_, v_a_3073_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_cacheInType_3094_);
v___x_3100_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3102_; 
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 9, v___x_3100_);
v___x_3102_ = v___x_3091_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_share_3079_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_maxFVar_3080_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_proofInstInfo_3081_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v_inferType_3082_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v_getLevel_3083_);
lean_ctor_set(v_reuseFailAlloc_3107_, 5, v_congrInfo_3084_);
lean_ctor_set(v_reuseFailAlloc_3107_, 6, v_defEqI_3085_);
lean_ctor_set(v_reuseFailAlloc_3107_, 7, v_extensions_3086_);
lean_ctor_set(v_reuseFailAlloc_3107_, 8, v_issues_3087_);
lean_ctor_set(v_reuseFailAlloc_3107_, 9, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3107_, 10, v_instanceOverrides_3088_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*11, v_debug_3089_);
v___x_3102_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = lean_st_ref_put(v_a_2740_, v___x_3102_);
if (v_isShared_3076_ == 0)
{
v___x_3105_ = v___x_3075_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3073_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 2);
return v___x_3072_;
}
}
}
else
{
lean_object* v___x_3112_; lean_object* v_canon_3113_; lean_object* v_cacheInType_3114_; lean_object* v___x_3115_; 
v___x_3112_ = lean_st_ref_get(v_a_2740_);
v_canon_3113_ = lean_ctor_get(v___x_3112_, 9);
lean_inc_ref(v_canon_3113_);
lean_dec(v___x_3112_);
v_cacheInType_3114_ = lean_ctor_get(v_canon_3113_, 1);
lean_inc_ref(v_cacheInType_3114_);
lean_dec_ref(v_canon_3113_);
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3114_, v_e_2737_);
lean_dec_ref(v_cacheInType_3114_);
if (lean_obj_tag(v___x_3115_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref_known(v_e_2737_, 2);
v_val_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_val_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 0);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_val_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
else
{
lean_object* v___x_3124_; 
lean_dec(v___x_3115_);
lean_inc_ref(v_e_2737_);
v___x_3124_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3163_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3163_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3163_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_canon_3130_; lean_object* v_share_3131_; lean_object* v_maxFVar_3132_; lean_object* v_proofInstInfo_3133_; lean_object* v_inferType_3134_; lean_object* v_getLevel_3135_; lean_object* v_congrInfo_3136_; lean_object* v_defEqI_3137_; lean_object* v_extensions_3138_; lean_object* v_issues_3139_; lean_object* v_instanceOverrides_3140_; uint8_t v_debug_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3162_; 
v___x_3129_ = lean_st_ref_take(v_a_2740_);
v_canon_3130_ = lean_ctor_get(v___x_3129_, 9);
v_share_3131_ = lean_ctor_get(v___x_3129_, 0);
v_maxFVar_3132_ = lean_ctor_get(v___x_3129_, 1);
v_proofInstInfo_3133_ = lean_ctor_get(v___x_3129_, 2);
v_inferType_3134_ = lean_ctor_get(v___x_3129_, 3);
v_getLevel_3135_ = lean_ctor_get(v___x_3129_, 4);
v_congrInfo_3136_ = lean_ctor_get(v___x_3129_, 5);
v_defEqI_3137_ = lean_ctor_get(v___x_3129_, 6);
v_extensions_3138_ = lean_ctor_get(v___x_3129_, 7);
v_issues_3139_ = lean_ctor_get(v___x_3129_, 8);
v_instanceOverrides_3140_ = lean_ctor_get(v___x_3129_, 10);
v_debug_3141_ = lean_ctor_get_uint8(v___x_3129_, sizeof(void*)*11);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3143_ = v___x_3129_;
v_isShared_3144_ = v_isSharedCheck_3162_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_instanceOverrides_3140_);
lean_inc(v_canon_3130_);
lean_inc(v_issues_3139_);
lean_inc(v_extensions_3138_);
lean_inc(v_defEqI_3137_);
lean_inc(v_congrInfo_3136_);
lean_inc(v_getLevel_3135_);
lean_inc(v_inferType_3134_);
lean_inc(v_proofInstInfo_3133_);
lean_inc(v_maxFVar_3132_);
lean_inc(v_share_3131_);
lean_dec(v___x_3129_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3162_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v_cache_3145_; lean_object* v_cacheInType_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3161_; 
v_cache_3145_ = lean_ctor_get(v_canon_3130_, 0);
v_cacheInType_3146_ = lean_ctor_get(v_canon_3130_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_canon_3130_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3148_ = v_canon_3130_;
v_isShared_3149_ = v_isSharedCheck_3161_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_cacheInType_3146_);
lean_inc(v_cache_3145_);
lean_dec(v_canon_3130_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3161_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_inc(v_a_3125_);
v___x_3150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3146_, v_e_2737_, v_a_3125_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v___x_3150_);
v___x_3152_ = v___x_3148_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_cache_3145_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3154_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 9, v___x_3152_);
v___x_3154_ = v___x_3143_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_share_3131_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_maxFVar_3132_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_proofInstInfo_3133_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_inferType_3134_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_getLevel_3135_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_congrInfo_3136_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_defEqI_3137_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_extensions_3138_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_issues_3139_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3159_, 10, v_instanceOverrides_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*11, v_debug_3141_);
v___x_3154_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_st_ref_put(v_a_2740_, v___x_3154_);
if (v_isShared_3128_ == 0)
{
v___x_3157_ = v___x_3127_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3125_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 2);
return v___x_3124_;
}
}
}
}
case 11:
{
if (v_a_2738_ == 0)
{
lean_object* v___x_3164_; lean_object* v_canon_3165_; lean_object* v_cache_3166_; lean_object* v___x_3167_; 
v___x_3164_ = lean_st_ref_get(v_a_2740_);
v_canon_3165_ = lean_ctor_get(v___x_3164_, 9);
lean_inc_ref(v_canon_3165_);
lean_dec(v___x_3164_);
v_cache_3166_ = lean_ctor_get(v_canon_3165_, 0);
lean_inc_ref(v_cache_3166_);
lean_dec_ref(v_canon_3165_);
v___x_3167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3166_, v_e_2737_);
lean_dec_ref(v_cache_3166_);
if (lean_obj_tag(v___x_3167_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_val_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 0);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_val_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
else
{
lean_object* v___x_3176_; 
lean_dec(v___x_3167_);
lean_inc_ref(v_e_2737_);
v___x_3176_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3215_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3215_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3215_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v_canon_3182_; lean_object* v_share_3183_; lean_object* v_maxFVar_3184_; lean_object* v_proofInstInfo_3185_; lean_object* v_inferType_3186_; lean_object* v_getLevel_3187_; lean_object* v_congrInfo_3188_; lean_object* v_defEqI_3189_; lean_object* v_extensions_3190_; lean_object* v_issues_3191_; lean_object* v_instanceOverrides_3192_; uint8_t v_debug_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3214_; 
v___x_3181_ = lean_st_ref_take(v_a_2740_);
v_canon_3182_ = lean_ctor_get(v___x_3181_, 9);
v_share_3183_ = lean_ctor_get(v___x_3181_, 0);
v_maxFVar_3184_ = lean_ctor_get(v___x_3181_, 1);
v_proofInstInfo_3185_ = lean_ctor_get(v___x_3181_, 2);
v_inferType_3186_ = lean_ctor_get(v___x_3181_, 3);
v_getLevel_3187_ = lean_ctor_get(v___x_3181_, 4);
v_congrInfo_3188_ = lean_ctor_get(v___x_3181_, 5);
v_defEqI_3189_ = lean_ctor_get(v___x_3181_, 6);
v_extensions_3190_ = lean_ctor_get(v___x_3181_, 7);
v_issues_3191_ = lean_ctor_get(v___x_3181_, 8);
v_instanceOverrides_3192_ = lean_ctor_get(v___x_3181_, 10);
v_debug_3193_ = lean_ctor_get_uint8(v___x_3181_, sizeof(void*)*11);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3195_ = v___x_3181_;
v_isShared_3196_ = v_isSharedCheck_3214_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_instanceOverrides_3192_);
lean_inc(v_canon_3182_);
lean_inc(v_issues_3191_);
lean_inc(v_extensions_3190_);
lean_inc(v_defEqI_3189_);
lean_inc(v_congrInfo_3188_);
lean_inc(v_getLevel_3187_);
lean_inc(v_inferType_3186_);
lean_inc(v_proofInstInfo_3185_);
lean_inc(v_maxFVar_3184_);
lean_inc(v_share_3183_);
lean_dec(v___x_3181_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3214_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_cache_3197_; lean_object* v_cacheInType_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3213_; 
v_cache_3197_ = lean_ctor_get(v_canon_3182_, 0);
v_cacheInType_3198_ = lean_ctor_get(v_canon_3182_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_canon_3182_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3200_ = v_canon_3182_;
v_isShared_3201_ = v_isSharedCheck_3213_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_cacheInType_3198_);
lean_inc(v_cache_3197_);
lean_dec(v_canon_3182_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3213_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_inc(v_a_3177_);
v___x_3202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3197_, v_e_2737_, v_a_3177_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3204_ = v___x_3200_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_cacheInType_3198_);
v___x_3204_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 9, v___x_3204_);
v___x_3206_ = v___x_3195_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_share_3183_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_maxFVar_3184_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_proofInstInfo_3185_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v_inferType_3186_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v_getLevel_3187_);
lean_ctor_set(v_reuseFailAlloc_3211_, 5, v_congrInfo_3188_);
lean_ctor_set(v_reuseFailAlloc_3211_, 6, v_defEqI_3189_);
lean_ctor_set(v_reuseFailAlloc_3211_, 7, v_extensions_3190_);
lean_ctor_set(v_reuseFailAlloc_3211_, 8, v_issues_3191_);
lean_ctor_set(v_reuseFailAlloc_3211_, 9, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 10, v_instanceOverrides_3192_);
lean_ctor_set_uint8(v_reuseFailAlloc_3211_, sizeof(void*)*11, v_debug_3193_);
v___x_3206_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_st_ref_put(v_a_2740_, v___x_3206_);
if (v_isShared_3180_ == 0)
{
v___x_3209_ = v___x_3179_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3177_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_3176_;
}
}
}
else
{
lean_object* v___x_3216_; lean_object* v_canon_3217_; lean_object* v_cacheInType_3218_; lean_object* v___x_3219_; 
v___x_3216_ = lean_st_ref_get(v_a_2740_);
v_canon_3217_ = lean_ctor_get(v___x_3216_, 9);
lean_inc_ref(v_canon_3217_);
lean_dec(v___x_3216_);
v_cacheInType_3218_ = lean_ctor_get(v_canon_3217_, 1);
lean_inc_ref(v_cacheInType_3218_);
lean_dec_ref(v_canon_3217_);
v___x_3219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3218_, v_e_2737_);
lean_dec_ref(v_cacheInType_3218_);
if (lean_obj_tag(v___x_3219_) == 1)
{
lean_object* v_val_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref_known(v_e_2737_, 3);
v_val_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_val_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_val_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v___x_3219_);
lean_inc_ref(v_e_2737_);
v___x_3228_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3267_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3267_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3267_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v_canon_3234_; lean_object* v_share_3235_; lean_object* v_maxFVar_3236_; lean_object* v_proofInstInfo_3237_; lean_object* v_inferType_3238_; lean_object* v_getLevel_3239_; lean_object* v_congrInfo_3240_; lean_object* v_defEqI_3241_; lean_object* v_extensions_3242_; lean_object* v_issues_3243_; lean_object* v_instanceOverrides_3244_; uint8_t v_debug_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3266_; 
v___x_3233_ = lean_st_ref_take(v_a_2740_);
v_canon_3234_ = lean_ctor_get(v___x_3233_, 9);
v_share_3235_ = lean_ctor_get(v___x_3233_, 0);
v_maxFVar_3236_ = lean_ctor_get(v___x_3233_, 1);
v_proofInstInfo_3237_ = lean_ctor_get(v___x_3233_, 2);
v_inferType_3238_ = lean_ctor_get(v___x_3233_, 3);
v_getLevel_3239_ = lean_ctor_get(v___x_3233_, 4);
v_congrInfo_3240_ = lean_ctor_get(v___x_3233_, 5);
v_defEqI_3241_ = lean_ctor_get(v___x_3233_, 6);
v_extensions_3242_ = lean_ctor_get(v___x_3233_, 7);
v_issues_3243_ = lean_ctor_get(v___x_3233_, 8);
v_instanceOverrides_3244_ = lean_ctor_get(v___x_3233_, 10);
v_debug_3245_ = lean_ctor_get_uint8(v___x_3233_, sizeof(void*)*11);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3247_ = v___x_3233_;
v_isShared_3248_ = v_isSharedCheck_3266_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_instanceOverrides_3244_);
lean_inc(v_canon_3234_);
lean_inc(v_issues_3243_);
lean_inc(v_extensions_3242_);
lean_inc(v_defEqI_3241_);
lean_inc(v_congrInfo_3240_);
lean_inc(v_getLevel_3239_);
lean_inc(v_inferType_3238_);
lean_inc(v_proofInstInfo_3237_);
lean_inc(v_maxFVar_3236_);
lean_inc(v_share_3235_);
lean_dec(v___x_3233_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3266_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v_cache_3249_; lean_object* v_cacheInType_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3265_; 
v_cache_3249_ = lean_ctor_get(v_canon_3234_, 0);
v_cacheInType_3250_ = lean_ctor_get(v_canon_3234_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_canon_3234_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3252_ = v_canon_3234_;
v_isShared_3253_ = v_isSharedCheck_3265_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_cacheInType_3250_);
lean_inc(v_cache_3249_);
lean_dec(v_canon_3234_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3265_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
lean_inc(v_a_3229_);
v___x_3254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3250_, v_e_2737_, v_a_3229_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v___x_3254_);
v___x_3256_ = v___x_3252_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_cache_3249_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3258_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 9, v___x_3256_);
v___x_3258_ = v___x_3247_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_share_3235_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_maxFVar_3236_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_proofInstInfo_3237_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_inferType_3238_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_getLevel_3239_);
lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_congrInfo_3240_);
lean_ctor_set(v_reuseFailAlloc_3263_, 6, v_defEqI_3241_);
lean_ctor_set(v_reuseFailAlloc_3263_, 7, v_extensions_3242_);
lean_ctor_set(v_reuseFailAlloc_3263_, 8, v_issues_3243_);
lean_ctor_set(v_reuseFailAlloc_3263_, 9, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3263_, 10, v_instanceOverrides_3244_);
lean_ctor_set_uint8(v_reuseFailAlloc_3263_, sizeof(void*)*11, v_debug_3245_);
v___x_3258_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_st_ref_put(v_a_2740_, v___x_3258_);
if (v_isShared_3232_ == 0)
{
v___x_3261_ = v___x_3231_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3229_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2737_, 3);
return v___x_3228_;
}
}
}
}
case 10:
{
lean_object* v_data_3268_; lean_object* v_expr_3269_; lean_object* v___x_3270_; 
v_data_3268_ = lean_ctor_get(v_e_2737_, 0);
v_expr_3269_ = lean_ctor_get(v_e_2737_, 1);
lean_inc_ref(v_expr_3269_);
v___x_3270_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3269_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3285_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3285_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3285_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
size_t v___x_3275_; size_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = lean_ptr_addr(v_expr_3269_);
v___x_3276_ = lean_ptr_addr(v_a_3271_);
v___x_3277_ = lean_usize_dec_eq(v___x_3275_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
lean_inc(v_data_3268_);
lean_dec_ref_known(v_e_2737_, 2);
v___x_3278_ = l_Lean_Expr_mdata___override(v_data_3268_, v_a_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3278_);
v___x_3280_ = v___x_3273_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
lean_object* v___x_3283_; 
lean_dec(v_a_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v_e_2737_);
v___x_3283_ = v___x_3273_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_e_2737_);
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
else
{
lean_dec_ref_known(v_e_2737_, 2);
return v___x_3270_;
}
}
default: 
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_e_2737_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3287_, uint8_t v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
if (v_a_3288_ == 0)
{
lean_object* v___x_3296_; 
lean_inc_ref(v_e_3287_);
v___x_3296_ = l_Lean_Meta_isProp(v_e_3287_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; uint8_t v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = lean_unbox(v_a_3297_);
lean_dec(v_a_3297_);
if (v___x_3298_ == 0)
{
uint8_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = 1;
v___x_3300_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3287_, v___x_3299_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3301_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_e_3287_);
v_a_3302_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3296_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3296_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3311_, lean_object* v_body_3312_, lean_object* v_x_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___y_68386__boxed_3322_; lean_object* v_res_3323_; 
v___y_68386__boxed_3322_ = lean_unbox(v___y_3314_);
v_res_3323_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3311_, v_body_3312_, v_x_3313_, v___y_68386__boxed_3322_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3324_, lean_object* v_e_3325_, uint8_t v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
if (lean_obj_tag(v_e_3325_) == 7)
{
lean_object* v_binderName_3334_; lean_object* v_binderType_3335_; lean_object* v_body_3336_; uint8_t v_binderInfo_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_binderName_3334_ = lean_ctor_get(v_e_3325_, 0);
lean_inc(v_binderName_3334_);
v_binderType_3335_ = lean_ctor_get(v_e_3325_, 1);
lean_inc_ref(v_binderType_3335_);
v_body_3336_ = lean_ctor_get(v_e_3325_, 2);
lean_inc_ref(v_body_3336_);
v_binderInfo_3337_ = lean_ctor_get_uint8(v_e_3325_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3325_, 3);
v___x_3338_ = lean_expr_instantiate_rev(v_binderType_3335_, v_fvars_3324_);
lean_dec_ref(v_binderType_3335_);
v___x_3339_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3338_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___f_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___f_3341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3341_, 0, v_fvars_3324_);
lean_closure_set(v___f_3341_, 1, v_body_3336_);
v___x_3342_ = 0;
v___x_3343_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3334_, v_binderInfo_3337_, v_a_3340_, v___f_3341_, v___x_3342_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
return v___x_3343_;
}
else
{
lean_dec_ref(v_body_3336_);
lean_dec(v_binderName_3334_);
lean_dec_ref(v_fvars_3324_);
return v___x_3339_;
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_expr_instantiate_rev(v_e_3325_, v_fvars_3324_);
lean_dec_ref(v_e_3325_);
v___x_3345_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3344_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = 0;
v___x_3348_ = 1;
v___x_3349_ = 1;
v___x_3350_ = l_Lean_Meta_mkForallFVars(v_fvars_3324_, v_a_3346_, v___x_3347_, v___x_3348_, v___x_3348_, v___x_3349_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
lean_dec_ref(v_fvars_3324_);
return v___x_3350_;
}
else
{
lean_dec_ref(v_fvars_3324_);
return v___x_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3351_, lean_object* v_body_3352_, lean_object* v_x_3353_, uint8_t v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = lean_array_push(v_fvars_3351_, v_x_3353_);
v___x_3363_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3362_, v_body_3352_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
uint8_t v_a_boxed_3373_; lean_object* v_res_3374_; 
v_a_boxed_3373_ = lean_unbox(v_a_3365_);
v_res_3374_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3364_, v_a_boxed_3373_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
uint8_t v_a_boxed_3384_; lean_object* v_res_3385_; 
v_a_boxed_3384_ = lean_unbox(v_a_3376_);
v_res_3385_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3375_, v_a_boxed_3384_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
uint8_t v_a_boxed_3395_; lean_object* v_res_3396_; 
v_a_boxed_3395_ = lean_unbox(v_a_3387_);
v_res_3396_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3386_, v_a_boxed_3395_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
uint8_t v_a_boxed_3406_; lean_object* v_res_3407_; 
v_a_boxed_3406_ = lean_unbox(v_a_3398_);
v_res_3407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3397_, v_a_boxed_3406_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
uint8_t v_a_boxed_3417_; lean_object* v_res_3418_; 
v_a_boxed_3417_ = lean_unbox(v_a_3409_);
v_res_3418_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3408_, v_a_boxed_3417_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3419_, lean_object* v_e_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
uint8_t v_a_boxed_3429_; lean_object* v_res_3430_; 
v_a_boxed_3429_ = lean_unbox(v_a_3421_);
v_res_3430_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3419_, v_e_3420_, v_a_boxed_3429_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3431_, lean_object* v_e_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
uint8_t v_a_boxed_3441_; lean_object* v_res_3442_; 
v_a_boxed_3441_ = lean_unbox(v_a_3433_);
v_res_3442_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3431_, v_e_3432_, v_a_boxed_3441_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3443_, lean_object* v_report_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
uint8_t v_report_boxed_3453_; uint8_t v_a_boxed_3454_; lean_object* v_res_3455_; 
v_report_boxed_3453_ = lean_unbox(v_report_3444_);
v_a_boxed_3454_ = lean_unbox(v_a_3445_);
v_res_3455_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3443_, v_report_boxed_3453_, v_a_boxed_3454_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
uint8_t v_a_boxed_3465_; lean_object* v_res_3466_; 
v_a_boxed_3465_ = lean_unbox(v_a_3457_);
v_res_3466_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3456_, v_a_boxed_3465_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3467_, lean_object* v_e_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
uint8_t v_a_boxed_3477_; lean_object* v_res_3478_; 
v_a_boxed_3477_ = lean_unbox(v_a_3469_);
v_res_3478_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3467_, v_e_3468_, v_a_boxed_3477_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3479_, lean_object* v_00_u03b1_3480_, lean_object* v_c_3481_, lean_object* v_a_3482_, lean_object* v_b_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
uint8_t v_a_boxed_3492_; lean_object* v_res_3493_; 
v_a_boxed_3492_ = lean_unbox(v_a_3484_);
v_res_3493_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3479_, v_00_u03b1_3480_, v_c_3481_, v_a_3482_, v_b_3483_, v_a_boxed_3492_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3494_, lean_object* v_00_u03b1_3495_, lean_object* v_c_3496_, lean_object* v_inst_3497_, lean_object* v_a_3498_, lean_object* v_b_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
uint8_t v_a_boxed_3508_; lean_object* v_res_3509_; 
v_a_boxed_3508_ = lean_unbox(v_a_3500_);
v_res_3509_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3494_, v_00_u03b1_3495_, v_c_3496_, v_inst_3497_, v_a_3498_, v_b_3499_, v_a_boxed_3508_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
uint8_t v_a_boxed_3519_; lean_object* v_res_3520_; 
v_a_boxed_3519_ = lean_unbox(v_a_3511_);
v_res_3520_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3510_, v_a_boxed_3519_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
uint8_t v_a_boxed_3530_; lean_object* v_res_3531_; 
v_a_boxed_3530_ = lean_unbox(v_a_3522_);
v_res_3531_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3521_, v_a_boxed_3530_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3532_, lean_object* v_prop_3533_, lean_object* v_inst_3534_, lean_object* v_e_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
uint8_t v_a_boxed_3544_; lean_object* v_res_3545_; 
v_a_boxed_3544_ = lean_unbox(v_a_3536_);
v_res_3545_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3532_, v_prop_3533_, v_inst_3534_, v_e_3535_, v_a_boxed_3544_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3546_, lean_object* v_report_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
uint8_t v_report_boxed_3556_; uint8_t v_a_boxed_3557_; lean_object* v_res_3558_; 
v_report_boxed_3556_ = lean_unbox(v_report_3547_);
v_a_boxed_3557_ = lean_unbox(v_a_3548_);
v_res_3558_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3546_, v_report_boxed_3556_, v_a_boxed_3557_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3559_, lean_object* v_prop_3560_, lean_object* v_h_3561_, lean_object* v_e_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
uint8_t v_a_boxed_3571_; lean_object* v_res_3572_; 
v_a_boxed_3571_ = lean_unbox(v_a_3563_);
v_res_3572_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3559_, v_prop_3560_, v_h_3561_, v_e_3562_, v_a_boxed_3571_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3573_, lean_object* v___x_3574_, lean_object* v_a_3575_, lean_object* v_b_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
uint8_t v___y_68758__boxed_3585_; lean_object* v_res_3586_; 
v___y_68758__boxed_3585_ = lean_unbox(v___y_3577_);
v_res_3586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3573_, v___x_3574_, v_a_3575_, v_b_3576_, v___y_68758__boxed_3585_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v___x_3574_);
lean_dec(v_upperBound_3573_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3587_, lean_object* v_a_3588_, lean_object* v___x_3589_, lean_object* v_snd_3590_, lean_object* v___x_3591_, lean_object* v_fst_3592_, lean_object* v_____r_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
uint8_t v___x_68823__boxed_3602_; uint8_t v___y_68825__boxed_3603_; lean_object* v_res_3604_; 
v___x_68823__boxed_3602_ = lean_unbox(v___x_3591_);
v___y_68825__boxed_3603_ = lean_unbox(v___y_3594_);
v_res_3604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3587_, v_a_3588_, v___x_3589_, v_snd_3590_, v___x_68823__boxed_3602_, v_fst_3592_, v_____r_3593_, v___y_68825__boxed_3603_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v_a_3588_);
lean_dec_ref(v___x_3587_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
uint8_t v_a_boxed_3614_; lean_object* v_res_3615_; 
v_a_boxed_3614_ = lean_unbox(v_a_3606_);
v_res_3615_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3605_, v_a_boxed_3614_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3616_, lean_object* v_prop_3617_, lean_object* v_h_3618_, lean_object* v_e_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
uint8_t v_a_boxed_3628_; lean_object* v_res_3629_; 
v_a_boxed_3628_ = lean_unbox(v_a_3620_);
v_res_3629_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3616_, v_prop_3617_, v_h_3618_, v_e_3619_, v_a_boxed_3628_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
uint8_t v___y_69017__boxed_3642_; lean_object* v_res_3643_; 
v___y_69017__boxed_3642_ = lean_unbox(v___y_3634_);
v_res_3643_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3630_, v_x_3631_, v_x_3632_, v_x_3633_, v___y_69017__boxed_3642_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
uint8_t v_a_boxed_3653_; lean_object* v_res_3654_; 
v_a_boxed_3653_ = lean_unbox(v_a_3645_);
v_res_3654_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3644_, v_a_boxed_3653_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3655_, uint8_t v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3655_, v___y_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v___y_71368__boxed_3674_; lean_object* v_res_3675_; 
v___y_71368__boxed_3674_ = lean_unbox(v___y_3666_);
v_res_3675_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3665_, v___y_71368__boxed_3674_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3676_, lean_object* v_name_3677_, lean_object* v_type_3678_, lean_object* v_val_3679_, lean_object* v_k_3680_, uint8_t v_nondep_3681_, uint8_t v_kind_3682_, uint8_t v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3677_, v_type_3678_, v_val_3679_, v_k_3680_, v_nondep_3681_, v_kind_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_name_3693_, lean_object* v_type_3694_, lean_object* v_val_3695_, lean_object* v_k_3696_, lean_object* v_nondep_3697_, lean_object* v_kind_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_nondep_boxed_3707_; uint8_t v_kind_boxed_3708_; uint8_t v___y_71394__boxed_3709_; lean_object* v_res_3710_; 
v_nondep_boxed_3707_ = lean_unbox(v_nondep_3697_);
v_kind_boxed_3708_ = lean_unbox(v_kind_3698_);
v___y_71394__boxed_3709_ = lean_unbox(v___y_3699_);
v_res_3710_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3692_, v_name_3693_, v_type_3694_, v_val_3695_, v_k_3696_, v_nondep_boxed_3707_, v_kind_boxed_3708_, v___y_71394__boxed_3709_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3711_, lean_object* v_name_3712_, uint8_t v_bi_3713_, lean_object* v_type_3714_, lean_object* v_k_3715_, uint8_t v_kind_3716_, uint8_t v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3712_, v_bi_3713_, v_type_3714_, v_k_3715_, v_kind_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3726_, lean_object* v_name_3727_, lean_object* v_bi_3728_, lean_object* v_type_3729_, lean_object* v_k_3730_, lean_object* v_kind_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
uint8_t v_bi_boxed_3740_; uint8_t v_kind_boxed_3741_; uint8_t v___y_71420__boxed_3742_; lean_object* v_res_3743_; 
v_bi_boxed_3740_ = lean_unbox(v_bi_3728_);
v_kind_boxed_3741_ = lean_unbox(v_kind_3731_);
v___y_71420__boxed_3742_ = lean_unbox(v___y_3732_);
v_res_3743_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3726_, v_name_3727_, v_bi_boxed_3740_, v_type_3729_, v_k_3730_, v_kind_boxed_3741_, v___y_71420__boxed_3742_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3744_, lean_object* v_m_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3745_, v_a_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3748_, lean_object* v_m_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3748_, v_m_3749_, v_a_3750_);
lean_dec_ref(v_a_3750_);
lean_dec_ref(v_m_3749_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3752_, lean_object* v_m_3753_, lean_object* v_a_3754_, lean_object* v_b_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3753_, v_a_3754_, v_b_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3757_, lean_object* v_msg_3758_, uint8_t v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3757_, v_msg_3758_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3768_, lean_object* v_msg_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
uint8_t v___y_71450__boxed_3778_; lean_object* v_res_3779_; 
v___y_71450__boxed_3778_ = lean_unbox(v___y_3770_);
v_res_3779_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3768_, v_msg_3769_, v___y_71450__boxed_3778_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3780_, lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v_inst_3783_, lean_object* v_R_3784_, lean_object* v_a_3785_, lean_object* v_b_3786_, lean_object* v_c_3787_, uint8_t v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3780_, v___x_3782_, v_a_3785_, v_b_3786_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3797_, lean_object* v___x_3798_, lean_object* v___x_3799_, lean_object* v_inst_3800_, lean_object* v_R_3801_, lean_object* v_a_3802_, lean_object* v_b_3803_, lean_object* v_c_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___y_71480__boxed_3813_; lean_object* v_res_3814_; 
v___y_71480__boxed_3813_ = lean_unbox(v___y_3805_);
v_res_3814_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3797_, v___x_3798_, v___x_3799_, v_inst_3800_, v_R_3801_, v_a_3802_, v_b_3803_, v_c_3804_, v___y_71480__boxed_3813_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3798_);
lean_dec(v_upperBound_3797_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3815_, lean_object* v_a_3816_, lean_object* v_x_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3816_, v_x_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3819_, lean_object* v_a_3820_, lean_object* v_x_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3819_, v_a_3820_, v_x_3821_);
lean_dec(v_x_3821_);
lean_dec_ref(v_a_3820_);
return v_res_3822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3823_, lean_object* v_a_3824_, lean_object* v_x_3825_){
_start:
{
uint8_t v___x_3826_; 
v___x_3826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3824_, v_x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3827_, lean_object* v_a_3828_, lean_object* v_x_3829_){
_start:
{
uint8_t v_res_3830_; lean_object* v_r_3831_; 
v_res_3830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3827_, v_a_3828_, v_x_3829_);
lean_dec(v_x_3829_);
lean_dec_ref(v_a_3828_);
v_r_3831_ = lean_box(v_res_3830_);
return v_r_3831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3832_, lean_object* v_data_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3835_, lean_object* v_a_3836_, lean_object* v_b_3837_, lean_object* v_x_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3836_, v_b_3837_, v_x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3840_, lean_object* v_i_3841_, lean_object* v_source_3842_, lean_object* v_target_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3841_, v_source_3842_, v_target_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3845_, lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3846_, v_x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3849_, lean_object* v_i_3850_, lean_object* v_arg_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3849_, v_i_3850_, v_arg_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3873_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3873_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3873_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_unbox(v_a_3858_);
lean_dec(v_a_3858_);
if (v___x_3862_ == 3)
{
uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3863_ = 0;
v___x_3864_ = lean_box(v___x_3863_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3864_);
v___x_3866_ = v___x_3860_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3868_ = 1;
v___x_3869_ = lean_box(v___x_3868_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3869_);
v___x_3871_ = v___x_3860_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3857_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3857_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3882_, lean_object* v_i_3883_, lean_object* v_arg_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3882_, v_i_3883_, v_arg_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_i_3883_);
lean_dec_ref(v_pinfos_3882_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3891_, lean_object* v_opts_3892_, lean_object* v_act_3893_, lean_object* v_decl_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
lean_inc(v___y_3898_);
lean_inc_ref(v___y_3897_);
lean_inc(v___y_3896_);
lean_inc_ref(v___y_3895_);
v___x_3902_ = lean_apply_6(v_act_3893_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
v___x_3903_ = l_Lean_profileitIOUnsafe___redArg(v_category_3891_, v_opts_3892_, v___x_3902_, v_decl_3894_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3904_, lean_object* v_opts_3905_, lean_object* v_act_3906_, lean_object* v_decl_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3904_, v_opts_3905_, v_act_3906_, v_decl_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec_ref(v_opts_3905_);
lean_dec_ref(v_category_3904_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3916_, lean_object* v_category_3917_, lean_object* v_opts_3918_, lean_object* v_act_3919_, lean_object* v_decl_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3917_, v_opts_3918_, v_act_3919_, v_decl_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3929_, lean_object* v_category_3930_, lean_object* v_opts_3931_, lean_object* v_act_3932_, lean_object* v_decl_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3929_, v_category_3930_, v_opts_3931_, v_act_3932_, v_decl_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v_opts_3931_);
lean_dec_ref(v_category_3930_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3942_, lean_object* v_e_3943_, uint8_t v___x_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_keyedConfig_3952_; uint8_t v_trackZetaDelta_3953_; lean_object* v_zetaDeltaSet_3954_; lean_object* v_lctx_3955_; lean_object* v_localInstances_3956_; lean_object* v_defEqCtx_x3f_3957_; lean_object* v_synthPendingDepth_3958_; lean_object* v_customCanUnfoldPredicate_x3f_3959_; uint8_t v_univApprox_3960_; uint8_t v_inTypeClassResolution_3961_; uint8_t v_cacheInferType_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_keyedConfig_3952_ = lean_ctor_get(v___y_3947_, 0);
v_trackZetaDelta_3953_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*7);
v_zetaDeltaSet_3954_ = lean_ctor_get(v___y_3947_, 1);
v_lctx_3955_ = lean_ctor_get(v___y_3947_, 2);
v_localInstances_3956_ = lean_ctor_get(v___y_3947_, 3);
v_defEqCtx_x3f_3957_ = lean_ctor_get(v___y_3947_, 4);
v_synthPendingDepth_3958_ = lean_ctor_get(v___y_3947_, 5);
v_customCanUnfoldPredicate_x3f_3959_ = lean_ctor_get(v___y_3947_, 6);
v_univApprox_3960_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3961_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*7 + 2);
v_cacheInferType_3962_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3952_);
v___x_3963_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3942_, v_keyedConfig_3952_);
lean_inc(v_customCanUnfoldPredicate_x3f_3959_);
lean_inc(v_synthPendingDepth_3958_);
lean_inc(v_defEqCtx_x3f_3957_);
lean_inc_ref(v_localInstances_3956_);
lean_inc_ref(v_lctx_3955_);
lean_inc(v_zetaDeltaSet_3954_);
v___x_3964_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v_zetaDeltaSet_3954_);
lean_ctor_set(v___x_3964_, 2, v_lctx_3955_);
lean_ctor_set(v___x_3964_, 3, v_localInstances_3956_);
lean_ctor_set(v___x_3964_, 4, v_defEqCtx_x3f_3957_);
lean_ctor_set(v___x_3964_, 5, v_synthPendingDepth_3958_);
lean_ctor_set(v___x_3964_, 6, v_customCanUnfoldPredicate_x3f_3959_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*7, v_trackZetaDelta_3953_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*7 + 1, v_univApprox_3960_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3961_);
lean_ctor_set_uint8(v___x_3964_, sizeof(void*)*7 + 3, v_cacheInferType_3962_);
v___x_3965_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3943_, v___x_3944_, v___y_3945_, v___y_3946_, v___x_3964_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec_ref_known(v___x_3964_, 7);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3966_, lean_object* v_e_3967_, lean_object* v___x_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
uint8_t v___x_1951__boxed_3976_; uint8_t v___x_1952__boxed_3977_; lean_object* v_res_3978_; 
v___x_1951__boxed_3976_ = lean_unbox(v___x_3966_);
v___x_1952__boxed_3977_ = lean_unbox(v___x_3968_);
v_res_3978_ = l_Lean_Meta_Sym_canon___lam__0(v___x_1951__boxed_3976_, v_e_3967_, v___x_1952__boxed_3977_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_options_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___f_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_options_3988_ = lean_ctor_get(v_a_3985_, 2);
v___x_3989_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3990_ = 0;
v___x_3991_ = 2;
v___x_3992_ = lean_box(v___x_3991_);
v___x_3993_ = lean_box(v___x_3990_);
v___f_3994_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3994_, 0, v___x_3992_);
lean_closure_set(v___f_3994_, 1, v_e_3980_);
lean_closure_set(v___f_3994_, 2, v___x_3993_);
v___x_3995_ = lean_box(0);
v___x_3996_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3989_, v_options_3988_, v___f_3994_, v___x_3995_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Meta_Sym_canon(v_e_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
return v_res_4005_;
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

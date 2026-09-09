// Lean compiler output
// Module: Lean.Meta.Sym.Canon
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ExprPtr import Lean.Meta.SynthInstance import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Arith.EvalNum import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters import Lean.Meta.LitValues import Lean.Meta.AppBuilder import Lean.Meta.Sym.Eta import Lean.Meta.WHNF import Init.Grind.Util
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1_value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_110_; uint8_t v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v_modified_172_; 
v___x_170_ = lean_array_get_size(v_args_95_);
v___x_171_ = lean_unsigned_to_nat(3u);
v_modified_172_ = lean_nat_dec_eq(v___x_170_, v___x_171_);
if (v_modified_172_ == 0)
{
lean_dec_ref(v_args_95_);
goto v___jp_101_;
}
else
{
uint8_t v_modified_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_modified_173_ = 0;
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_array_fget_borrowed(v_args_95_, v___x_174_);
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_177_ = l_Lean_Expr_isAppOf(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
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
v_modified_141_ = v_modified_172_;
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_112_, v___y_113_);
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
v___y_105_ = v___y_110_;
v___y_106_ = v___y_111_;
goto v___jp_104_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_fget_borrowed(v___y_110_, v___x_120_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Int_mkType;
v___x_125_ = lean_array_fset(v___y_110_, v___x_120_, v___x_124_);
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
v___y_105_ = v___y_110_;
v___y_106_ = v___y_111_;
goto v___jp_104_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v___y_110_);
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
v___y_110_ = v_args_140_;
v___y_111_ = v_modified_141_;
v___y_112_ = v_inst_144_;
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
v___y_110_ = v_args_140_;
v___y_111_ = v_modified_141_;
v___y_112_ = v_inst_144_;
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
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1));
v___x_203_ = l_Lean_mkConst(v___x_202_, v___x_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(lean_object* v_e_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_getBitVecValue_x3f(v_e_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_249_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_249_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_249_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_249_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
if (lean_obj_tag(v_a_211_) == 1)
{
lean_object* v_val_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_244_; 
lean_del_object(v___x_213_);
v_val_215_ = lean_ctor_get(v_a_211_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_a_211_);
if (v_isSharedCheck_244_ == 0)
{
v___x_217_ = v_a_211_;
v_isShared_218_ = v_isSharedCheck_244_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_val_215_);
lean_dec(v_a_211_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_244_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_fst_219_ = lean_ctor_get(v_val_215_, 0);
lean_inc(v_fst_219_);
v_snd_220_ = lean_ctor_get(v_val_215_, 1);
lean_inc(v_snd_220_);
lean_dec(v_val_215_);
v___x_221_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2);
v___x_222_ = l_Lean_mkNatLit(v_fst_219_);
v___x_223_ = l_Lean_Expr_app___override(v___x_221_, v___x_222_);
v___x_224_ = l_Lean_Meta_mkNumeral(v___x_223_, v_snd_220_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_235_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_235_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v_a_225_);
v___x_230_ = v___x_217_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_del_object(v___x_217_);
v_a_236_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_224_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_224_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v_a_211_);
v___x_245_ = lean_box(0);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_245_);
v___x_247_ = v___x_213_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_210_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_210_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___boxed(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_264_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_box(0);
v___x_279_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5));
v___x_280_ = l_Lean_mkConst(v___x_279_, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
lean_inc_ref(v_e_281_);
v___x_287_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_281_, v_a_283_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_460_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_460_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_460_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_460_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Expr_cleanupAnnotations(v_a_288_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v___x_297_);
lean_dec_ref(v_e_281_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_arg_299_ = lean_ctor_get(v___x_297_, 1);
lean_inc_ref(v_arg_299_);
v___x_300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_301_ = l_Lean_Expr_isApp(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_300_);
lean_dec_ref(v_arg_299_);
lean_dec_ref(v_e_281_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_arg_302_ = lean_ctor_get(v___x_300_, 1);
lean_inc_ref(v_arg_302_);
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_300_);
v___x_304_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_Expr_isApp(v___x_303_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_299_);
lean_dec_ref(v_e_281_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_arg_307_ = lean_ctor_get(v___x_303_, 1);
lean_inc_ref(v_arg_307_);
v___x_308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_310_ = l_Lean_Expr_isConstOf(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
lean_dec_ref(v_arg_302_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_308_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_299_);
v___x_313_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_314_ = l_Lean_Expr_isConstOf(v___x_308_, v___x_313_);
lean_dec_ref(v___x_308_);
if (v___x_314_ == 0)
{
lean_dec_ref(v_e_281_);
goto v___jp_292_;
}
else
{
lean_object* v___x_315_; 
lean_del_object(v___x_290_);
v___x_315_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_315_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec_ref(v___x_308_);
lean_del_object(v___x_290_);
lean_dec_ref(v_e_281_);
v___x_316_ = l_Lean_Meta_getNatValue_x3f(v_arg_307_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_307_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_379_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_379_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_379_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_379_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
if (lean_obj_tag(v_a_317_) == 1)
{
lean_object* v_val_321_; lean_object* v___x_322_; 
lean_del_object(v___x_319_);
v_val_321_ = lean_ctor_get(v_a_317_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v_a_317_, 1);
v___x_322_ = l_Lean_Meta_getNatValue_x3f(v_arg_299_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_299_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_366_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_366_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_366_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_366_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
if (lean_obj_tag(v_a_323_) == 1)
{
lean_object* v_val_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_361_; 
v_val_327_ = lean_ctor_get(v_a_323_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_323_);
if (v_isSharedCheck_361_ == 0)
{
v___x_329_ = v_a_323_;
v_isShared_330_ = v_isSharedCheck_361_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_val_327_);
lean_dec(v_a_323_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_361_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_nat_dec_eq(v_val_321_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_del_object(v___x_325_);
v___x_333_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6);
lean_inc(v_val_321_);
v___x_334_ = l_Lean_mkNatLit(v_val_321_);
v___x_335_ = l_Lean_Expr_app___override(v___x_333_, v___x_334_);
v___x_336_ = lean_nat_mod(v_val_327_, v_val_321_);
lean_dec(v_val_321_);
lean_dec(v_val_327_);
v___x_337_ = l_Lean_Meta_mkNumeral(v___x_335_, v___x_336_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_a_338_);
v___x_343_ = v___x_329_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_del_object(v___x_329_);
v_a_349_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_337_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_337_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_del_object(v___x_329_);
lean_dec(v_val_327_);
lean_dec(v_val_321_);
v___x_357_ = lean_box(0);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_357_);
v___x_359_ = v___x_325_;
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
}
else
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_dec(v_a_323_);
lean_dec(v_val_321_);
v___x_362_ = lean_box(0);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_362_);
v___x_364_ = v___x_325_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_val_321_);
v_a_367_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_322_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_322_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_dec(v_a_317_);
lean_dec_ref(v_arg_299_);
v___x_375_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_375_);
v___x_377_ = v___x_319_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_arg_299_);
v_a_380_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_316_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_316_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_308_);
lean_dec_ref(v_arg_299_);
lean_del_object(v___x_290_);
lean_dec_ref(v_e_281_);
lean_inc_ref(v_arg_307_);
v___x_388_ = l_Lean_Meta_getLitValueModulus_x3f(v_arg_307_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_450_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_450_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_450_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_450_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
if (lean_obj_tag(v_a_389_) == 1)
{
lean_object* v_val_393_; lean_object* v___x_394_; 
v_val_393_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v_a_389_, 1);
v___x_394_ = l_Lean_Meta_getNatValue_x3f(v_arg_302_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_302_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_437_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_437_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_437_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_437_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
if (lean_obj_tag(v_a_395_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_432_; 
lean_del_object(v___x_391_);
v_val_404_ = lean_ctor_get(v_a_395_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_432_ == 0)
{
v___x_406_ = v_a_395_;
v_isShared_407_ = v_isSharedCheck_432_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v_a_395_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_432_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_nat_dec_eq(v_val_393_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_val_404_, v_val_393_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_del_object(v___x_397_);
v___x_411_ = lean_nat_mod(v_val_404_, v_val_393_);
lean_dec(v_val_393_);
lean_dec(v_val_404_);
v___x_412_ = l_Lean_Meta_mkNumeral(v_arg_307_, v___x_411_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_423_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_423_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_413_);
v___x_418_ = v___x_406_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
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
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_406_);
v_a_424_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_412_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_412_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_del_object(v___x_406_);
lean_dec(v_val_404_);
lean_dec(v_val_393_);
lean_dec_ref(v_arg_307_);
goto v___jp_399_;
}
}
else
{
lean_del_object(v___x_406_);
lean_dec(v_val_404_);
lean_dec(v_val_393_);
lean_dec_ref(v_arg_307_);
goto v___jp_399_;
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_del_object(v___x_397_);
lean_dec(v_a_395_);
lean_dec(v_val_393_);
lean_dec_ref(v_arg_307_);
v___x_433_ = lean_box(0);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_433_);
v___x_435_ = v___x_391_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
v___jp_399_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_val_393_);
lean_del_object(v___x_391_);
lean_dec_ref(v_arg_307_);
v_a_438_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_394_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_394_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec(v_a_389_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_302_);
v___x_446_ = lean_box(0);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_446_);
v___x_448_ = v___x_391_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_302_);
v_a_451_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_388_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_388_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_299_);
lean_del_object(v___x_290_);
v___x_459_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_459_;
}
}
}
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_box(0);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_293_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_e_281_);
v_a_461_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_287_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_287_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_478_, lean_object* v_k_479_, uint8_t v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_480_ == 0)
{
lean_object* v___x_490_; lean_object* v_canon_491_; lean_object* v_cache_492_; lean_object* v___x_493_; 
v___x_490_ = lean_st_ref_get(v_a_482_);
v_canon_491_ = lean_ctor_get(v___x_490_, 9);
lean_inc_ref(v_canon_491_);
lean_dec(v___x_490_);
v_cache_492_ = lean_ctor_get(v_canon_491_, 0);
lean_inc_ref(v_cache_492_);
lean_dec_ref(v_canon_491_);
lean_inc_ref(v_e_478_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_488_, v___x_489_, v_cache_492_, v_e_478_);
lean_dec_ref(v_cache_492_);
if (lean_obj_tag(v___x_493_) == 1)
{
lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_k_479_);
lean_dec_ref(v_e_478_);
v_val_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 0);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_val_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_493_);
v___x_502_ = lean_box(v_a_480_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
v___x_503_ = lean_apply_8(v_k_479_, v___x_502_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, lean_box(0));
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_542_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_542_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_542_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_542_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v_canon_509_; lean_object* v_share_510_; lean_object* v_maxFVar_511_; lean_object* v_proofInstInfo_512_; lean_object* v_inferType_513_; lean_object* v_getLevel_514_; lean_object* v_congrInfo_515_; lean_object* v_defEqI_516_; lean_object* v_extensions_517_; lean_object* v_issues_518_; lean_object* v_instanceOverrides_519_; uint8_t v_debug_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_541_; 
v___x_508_ = lean_st_ref_take(v_a_482_);
v_canon_509_ = lean_ctor_get(v___x_508_, 9);
v_share_510_ = lean_ctor_get(v___x_508_, 0);
v_maxFVar_511_ = lean_ctor_get(v___x_508_, 1);
v_proofInstInfo_512_ = lean_ctor_get(v___x_508_, 2);
v_inferType_513_ = lean_ctor_get(v___x_508_, 3);
v_getLevel_514_ = lean_ctor_get(v___x_508_, 4);
v_congrInfo_515_ = lean_ctor_get(v___x_508_, 5);
v_defEqI_516_ = lean_ctor_get(v___x_508_, 6);
v_extensions_517_ = lean_ctor_get(v___x_508_, 7);
v_issues_518_ = lean_ctor_get(v___x_508_, 8);
v_instanceOverrides_519_ = lean_ctor_get(v___x_508_, 10);
v_debug_520_ = lean_ctor_get_uint8(v___x_508_, sizeof(void*)*11);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_541_ == 0)
{
v___x_522_ = v___x_508_;
v_isShared_523_ = v_isSharedCheck_541_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_instanceOverrides_519_);
lean_inc(v_canon_509_);
lean_inc(v_issues_518_);
lean_inc(v_extensions_517_);
lean_inc(v_defEqI_516_);
lean_inc(v_congrInfo_515_);
lean_inc(v_getLevel_514_);
lean_inc(v_inferType_513_);
lean_inc(v_proofInstInfo_512_);
lean_inc(v_maxFVar_511_);
lean_inc(v_share_510_);
lean_dec(v___x_508_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_541_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_cache_524_; lean_object* v_cacheInType_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_540_; 
v_cache_524_ = lean_ctor_get(v_canon_509_, 0);
v_cacheInType_525_ = lean_ctor_get(v_canon_509_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_canon_509_);
if (v_isSharedCheck_540_ == 0)
{
v___x_527_ = v_canon_509_;
v_isShared_528_ = v_isSharedCheck_540_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_cacheInType_525_);
lean_inc(v_cache_524_);
lean_dec(v_canon_509_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_540_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_a_504_);
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_488_, v___x_489_, v_cache_524_, v_e_478_, v_a_504_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_cacheInType_525_);
v___x_531_ = v_reuseFailAlloc_539_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 9, v___x_531_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_share_510_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_maxFVar_511_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_proofInstInfo_512_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_inferType_513_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_getLevel_514_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v_congrInfo_515_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_defEqI_516_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_extensions_517_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_issues_518_);
lean_ctor_set(v_reuseFailAlloc_538_, 9, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_538_, 10, v_instanceOverrides_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*11, v_debug_520_);
v___x_533_ = v_reuseFailAlloc_538_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_st_ref_put(v_a_482_, v___x_533_);
if (v_isShared_507_ == 0)
{
v___x_536_ = v___x_506_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_504_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_478_);
return v___x_503_;
}
}
}
else
{
lean_object* v___x_543_; lean_object* v_canon_544_; lean_object* v_cacheInType_545_; lean_object* v___x_546_; 
v___x_543_ = lean_st_ref_get(v_a_482_);
v_canon_544_ = lean_ctor_get(v___x_543_, 9);
lean_inc_ref(v_canon_544_);
lean_dec(v___x_543_);
v_cacheInType_545_ = lean_ctor_get(v_canon_544_, 1);
lean_inc_ref(v_cacheInType_545_);
lean_dec_ref(v_canon_544_);
lean_inc_ref(v_e_478_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_488_, v___x_489_, v_cacheInType_545_, v_e_478_);
lean_dec_ref(v_cacheInType_545_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_k_479_);
lean_dec_ref(v_e_478_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_val_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_546_);
v___x_555_ = lean_box(v_a_480_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
v___x_556_ = lean_apply_8(v_k_479_, v___x_555_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, lean_box(0));
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_595_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_595_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v_canon_562_; lean_object* v_share_563_; lean_object* v_maxFVar_564_; lean_object* v_proofInstInfo_565_; lean_object* v_inferType_566_; lean_object* v_getLevel_567_; lean_object* v_congrInfo_568_; lean_object* v_defEqI_569_; lean_object* v_extensions_570_; lean_object* v_issues_571_; lean_object* v_instanceOverrides_572_; uint8_t v_debug_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_594_; 
v___x_561_ = lean_st_ref_take(v_a_482_);
v_canon_562_ = lean_ctor_get(v___x_561_, 9);
v_share_563_ = lean_ctor_get(v___x_561_, 0);
v_maxFVar_564_ = lean_ctor_get(v___x_561_, 1);
v_proofInstInfo_565_ = lean_ctor_get(v___x_561_, 2);
v_inferType_566_ = lean_ctor_get(v___x_561_, 3);
v_getLevel_567_ = lean_ctor_get(v___x_561_, 4);
v_congrInfo_568_ = lean_ctor_get(v___x_561_, 5);
v_defEqI_569_ = lean_ctor_get(v___x_561_, 6);
v_extensions_570_ = lean_ctor_get(v___x_561_, 7);
v_issues_571_ = lean_ctor_get(v___x_561_, 8);
v_instanceOverrides_572_ = lean_ctor_get(v___x_561_, 10);
v_debug_573_ = lean_ctor_get_uint8(v___x_561_, sizeof(void*)*11);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_594_ == 0)
{
v___x_575_ = v___x_561_;
v_isShared_576_ = v_isSharedCheck_594_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_instanceOverrides_572_);
lean_inc(v_canon_562_);
lean_inc(v_issues_571_);
lean_inc(v_extensions_570_);
lean_inc(v_defEqI_569_);
lean_inc(v_congrInfo_568_);
lean_inc(v_getLevel_567_);
lean_inc(v_inferType_566_);
lean_inc(v_proofInstInfo_565_);
lean_inc(v_maxFVar_564_);
lean_inc(v_share_563_);
lean_dec(v___x_561_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_594_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_cache_577_; lean_object* v_cacheInType_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_593_; 
v_cache_577_ = lean_ctor_get(v_canon_562_, 0);
v_cacheInType_578_ = lean_ctor_get(v_canon_562_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_canon_562_);
if (v_isSharedCheck_593_ == 0)
{
v___x_580_ = v_canon_562_;
v_isShared_581_ = v_isSharedCheck_593_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_cacheInType_578_);
lean_inc(v_cache_577_);
lean_dec(v_canon_562_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_593_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
lean_inc(v_a_557_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_488_, v___x_489_, v_cacheInType_578_, v_e_478_, v_a_557_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_592_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 9, v___x_584_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_share_563_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_maxFVar_564_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_proofInstInfo_565_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_inferType_566_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_getLevel_567_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_congrInfo_568_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_defEqI_569_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_extensions_570_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_issues_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 9, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_591_, 10, v_instanceOverrides_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*11, v_debug_573_);
v___x_586_ = v_reuseFailAlloc_591_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_st_ref_put(v_a_482_, v___x_586_);
if (v_isShared_560_ == 0)
{
v___x_589_ = v___x_559_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_557_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_478_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_596_, lean_object* v_k_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_a_boxed_606_; lean_object* v_res_607_; 
v_a_boxed_606_ = lean_unbox(v_a_598_);
v_res_607_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_596_, v_k_597_, v_a_boxed_606_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_Expr_cleanupAnnotations(v_e_614_);
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Expr_isApp(v___x_615_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_615_);
return v___x_618_;
}
else
{
lean_object* v_arg_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_arg_619_ = lean_ctor_get(v___x_615_, 1);
lean_inc_ref(v_arg_619_);
v___x_620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_615_);
v___x_621_ = l_Lean_Expr_isApp(v___x_620_);
if (v___x_621_ == 0)
{
lean_dec_ref(v___x_620_);
lean_dec_ref(v_arg_619_);
return v___x_621_;
}
else
{
lean_object* v_arg_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_arg_622_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_arg_622_);
v___x_623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_620_);
v___x_624_ = l_Lean_Expr_isApp(v___x_623_);
if (v___x_624_ == 0)
{
lean_dec_ref(v___x_623_);
lean_dec_ref(v_arg_622_);
lean_dec_ref(v_arg_619_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_623_);
v___x_626_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_627_ = l_Lean_Expr_isConstOf(v___x_625_, v___x_626_);
lean_dec_ref(v___x_625_);
if (v___x_627_ == 0)
{
lean_dec_ref(v_arg_622_);
lean_dec_ref(v_arg_619_);
return v___x_627_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = l_Lean_Expr_isBoolTrue(v_arg_622_);
if (v___x_628_ == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_628_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_Expr_isBoolTrue(v_arg_619_);
return v___x_629_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_615_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_630_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = l_Lean_Expr_cleanupAnnotations(v_e_636_);
v___x_638_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_639_ = l_Lean_Expr_isConstOf(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_isApp(v___x_637_);
if (v___x_640_ == 0)
{
lean_dec_ref(v___x_637_);
return v___x_640_;
}
else
{
lean_object* v_arg_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_arg_641_ = lean_ctor_get(v___x_637_, 1);
lean_inc_ref(v_arg_641_);
v___x_642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_637_);
v___x_643_ = l_Lean_Expr_isApp(v___x_642_);
if (v___x_643_ == 0)
{
lean_dec_ref(v___x_642_);
lean_dec_ref(v_arg_641_);
return v___x_643_;
}
else
{
lean_object* v_arg_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_arg_644_ = lean_ctor_get(v___x_642_, 1);
lean_inc_ref(v_arg_644_);
v___x_645_ = l_Lean_Expr_appFnCleanup___redArg(v___x_642_);
v___x_646_ = l_Lean_Expr_isApp(v___x_645_);
if (v___x_646_ == 0)
{
lean_dec_ref(v___x_645_);
lean_dec_ref(v_arg_644_);
lean_dec_ref(v_arg_641_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_645_);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_649_ = l_Lean_Expr_isConstOf(v___x_647_, v___x_648_);
lean_dec_ref(v___x_647_);
if (v___x_649_ == 0)
{
lean_dec_ref(v_arg_644_);
lean_dec_ref(v_arg_641_);
return v___x_649_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Expr_isBoolFalse(v_arg_644_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_arg_641_);
return v___x_650_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_isBoolTrue(v_arg_641_);
return v___x_651_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_637_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_652_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_655_){
_start:
{
switch(v_x_655_)
{
case 0:
{
lean_object* v___x_656_; 
v___x_656_ = lean_unsigned_to_nat(0u);
return v___x_656_;
}
case 1:
{
lean_object* v___x_657_; 
v___x_657_ = lean_unsigned_to_nat(1u);
return v___x_657_;
}
case 2:
{
lean_object* v___x_658_; 
v___x_658_ = lean_unsigned_to_nat(2u);
return v___x_658_;
}
default: 
{
lean_object* v___x_659_; 
v___x_659_ = lean_unsigned_to_nat(3u);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_660_){
_start:
{
uint8_t v_x_boxed_661_; lean_object* v_res_662_; 
v_x_boxed_661_ = lean_unbox(v_x_660_);
v_res_662_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_663_){
_start:
{
lean_inc(v_k_663_);
return v_k_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_664_);
lean_dec(v_k_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_666_, lean_object* v_ctorIdx_667_, uint8_t v_t_668_, lean_object* v_h_669_, lean_object* v_k_670_){
_start:
{
lean_inc(v_k_670_);
return v_k_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_671_, lean_object* v_ctorIdx_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_k_675_){
_start:
{
uint8_t v_t_boxed_676_; lean_object* v_res_677_; 
v_t_boxed_676_ = lean_unbox(v_t_673_);
v_res_677_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_671_, v_ctorIdx_672_, v_t_boxed_676_, v_h_674_, v_k_675_);
lean_dec(v_k_675_);
lean_dec(v_ctorIdx_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_678_){
_start:
{
lean_inc(v_canonType_678_);
return v_canonType_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_679_);
lean_dec(v_canonType_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_681_, uint8_t v_t_682_, lean_object* v_h_683_, lean_object* v_canonType_684_){
_start:
{
lean_inc(v_canonType_684_);
return v_canonType_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_685_, lean_object* v_t_686_, lean_object* v_h_687_, lean_object* v_canonType_688_){
_start:
{
uint8_t v_t_boxed_689_; lean_object* v_res_690_; 
v_t_boxed_689_ = lean_unbox(v_t_686_);
v_res_690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_685_, v_t_boxed_689_, v_h_687_, v_canonType_688_);
lean_dec(v_canonType_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_691_){
_start:
{
lean_inc(v_canonInst_691_);
return v_canonInst_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_692_);
lean_dec(v_canonInst_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_694_, uint8_t v_t_695_, lean_object* v_h_696_, lean_object* v_canonInst_697_){
_start:
{
lean_inc(v_canonInst_697_);
return v_canonInst_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_698_, lean_object* v_t_699_, lean_object* v_h_700_, lean_object* v_canonInst_701_){
_start:
{
uint8_t v_t_boxed_702_; lean_object* v_res_703_; 
v_t_boxed_702_ = lean_unbox(v_t_699_);
v_res_703_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_698_, v_t_boxed_702_, v_h_700_, v_canonInst_701_);
lean_dec(v_canonInst_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_704_){
_start:
{
lean_inc(v_canonImplicit_704_);
return v_canonImplicit_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_705_);
lean_dec(v_canonImplicit_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_707_, uint8_t v_t_708_, lean_object* v_h_709_, lean_object* v_canonImplicit_710_){
_start:
{
lean_inc(v_canonImplicit_710_);
return v_canonImplicit_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_711_, lean_object* v_t_712_, lean_object* v_h_713_, lean_object* v_canonImplicit_714_){
_start:
{
uint8_t v_t_boxed_715_; lean_object* v_res_716_; 
v_t_boxed_715_ = lean_unbox(v_t_712_);
v_res_716_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_711_, v_t_boxed_715_, v_h_713_, v_canonImplicit_714_);
lean_dec(v_canonImplicit_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_717_){
_start:
{
lean_inc(v_visit_717_);
return v_visit_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_718_);
lean_dec(v_visit_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_720_, uint8_t v_t_721_, lean_object* v_h_722_, lean_object* v_visit_723_){
_start:
{
lean_inc(v_visit_723_);
return v_visit_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_724_, lean_object* v_t_725_, lean_object* v_h_726_, lean_object* v_visit_727_){
_start:
{
uint8_t v_t_boxed_728_; lean_object* v_res_729_; 
v_t_boxed_728_ = lean_unbox(v_t_725_);
v_res_729_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_724_, v_t_boxed_728_, v_h_726_, v_visit_727_);
lean_dec(v_visit_727_);
return v_res_729_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = 0;
return v___x_730_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = 0;
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_744_, lean_object* v_x_745_){
_start:
{
switch(v_r_744_)
{
case 0:
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_746_;
}
case 1:
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_747_;
}
case 2:
{
lean_object* v___x_748_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_748_;
}
default: 
{
lean_object* v___x_749_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_r_boxed_752_; lean_object* v_res_753_; 
v_r_boxed_752_ = lean_unbox(v_r_750_);
v_res_753_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_752_, v_x_751_);
lean_dec(v_x_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_756_, lean_object* v_i_757_, lean_object* v_arg_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_array_get_size(v_pinfos_756_);
v___x_815_ = lean_nat_dec_lt(v_i_757_, v___x_814_);
if (v___x_815_ == 0)
{
v___y_765_ = v_a_759_;
v___y_766_ = v_a_760_;
v___y_767_ = v_a_761_;
v___y_768_ = v_a_762_;
goto v___jp_764_;
}
else
{
lean_object* v_pinfo_816_; uint8_t v_isInstance_817_; 
v_pinfo_816_ = lean_array_fget_borrowed(v_pinfos_756_, v_i_757_);
v_isInstance_817_ = lean_ctor_get_uint8(v_pinfo_816_, sizeof(void*)*1 + 4);
if (v_isInstance_817_ == 0)
{
uint8_t v_isProp_818_; 
v_isProp_818_ = lean_ctor_get_uint8(v_pinfo_816_, sizeof(void*)*1 + 2);
if (v_isProp_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_816_);
if (v___x_819_ == 0)
{
v___y_765_ = v_a_759_;
v___y_766_ = v_a_760_;
v___y_767_ = v_a_761_;
v___y_768_ = v_a_762_;
goto v___jp_764_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_isTypeFormer(v_arg_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_836_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_836_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_836_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_836_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = 2;
v___x_827_ = lean_box(v___x_826_);
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
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = 0;
v___x_832_ = lean_box(v___x_831_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_832_);
v___x_834_ = v___x_823_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
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
v_a_837_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_820_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_820_);
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
}
else
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v_arg_758_);
v___x_845_ = 3;
v___x_846_ = lean_box(v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
else
{
uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v_arg_758_);
v___x_848_ = 1;
v___x_849_ = lean_box(v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
v___jp_764_:
{
lean_object* v___x_769_; 
lean_inc_ref(v_arg_758_);
v___x_769_ = l_Lean_Meta_isProp(v_arg_758_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_805_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_805_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_805_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_805_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint8_t v___x_774_; 
v___x_774_ = lean_unbox(v_a_770_);
lean_dec(v_a_770_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_del_object(v___x_772_);
v___x_775_ = l_Lean_Meta_isTypeFormer(v_arg_758_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_791_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_791_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_791_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_791_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
uint8_t v___x_780_; 
v___x_780_ = lean_unbox(v_a_776_);
lean_dec(v_a_776_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = 3;
v___x_782_ = lean_box(v___x_781_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_782_);
v___x_784_ = v___x_778_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = 0;
v___x_787_ = lean_box(v___x_786_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_787_);
v___x_789_ = v___x_778_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_775_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_775_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec_ref(v_arg_758_);
v___x_800_ = 3;
v___x_801_ = lean_box(v___x_800_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_801_);
v___x_803_ = v___x_772_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
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
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_arg_758_);
v_a_806_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_769_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_769_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_851_, lean_object* v_i_852_, lean_object* v_arg_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_851_, v_i_852_, v_arg_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_i_852_);
lean_dec_ref(v_pinfos_851_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_860_, lean_object* v_offset_861_){
_start:
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_dec_eq(v_offset_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Lean_mkNatLit(v_offset_861_);
v___x_865_ = l_Lean_mkNatAdd(v_e_860_, v___x_864_);
return v___x_865_;
}
else
{
lean_dec(v_offset_861_);
return v_e_860_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_866_; lean_object* v_dummy_867_; 
v___x_866_ = lean_box(0);
v_dummy_867_ = l_Lean_Expr_sort___override(v___x_866_);
return v_dummy_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_868_, lean_object* v_e_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
uint8_t v_fromClass_875_; 
v_fromClass_875_ = lean_ctor_get_uint8(v_info_868_, sizeof(void*)*3);
if (v_fromClass_875_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_869_, v_fromClass_875_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_912_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_912_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_912_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_912_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_del_object(v___x_879_);
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_877_, 1);
v___x_882_ = l_Lean_Expr_getAppFn(v_val_881_);
v___x_883_ = l_Lean_Meta_reduceProj_x3f(v___x_882_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
if (lean_obj_tag(v_a_884_) == 0)
{
lean_dec(v_val_881_);
return v___x_883_;
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_906_; 
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_907_);
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_906_;
goto v_resetjp_885_;
}
else
{
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_906_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_905_; 
v_val_888_ = lean_ctor_get(v_a_884_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_a_884_);
if (v_isSharedCheck_905_ == 0)
{
v___x_890_ = v_a_884_;
v_isShared_891_ = v_isSharedCheck_905_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_val_888_);
lean_dec(v_a_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_905_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_dummy_892_; lean_object* v_nargs_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_dummy_892_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_893_ = l_Lean_Expr_getAppNumArgs(v_val_881_);
lean_inc(v_nargs_893_);
v___x_894_ = lean_mk_array(v_nargs_893_, v_dummy_892_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_sub(v_nargs_893_, v___x_895_);
lean_dec(v_nargs_893_);
v___x_897_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_881_, v___x_894_, v___x_896_);
v___x_898_ = l_Lean_mkAppN(v_val_888_, v___x_897_);
lean_dec_ref(v___x_897_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_898_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_900_);
v___x_902_ = v___x_886_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_dec(v_val_881_);
return v___x_883_;
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
lean_dec(v_a_877_);
v___x_908_ = lean_box(0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_908_);
v___x_910_ = v___x_879_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
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
else
{
return v___x_876_;
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_e_869_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_915_, lean_object* v_e_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_915_, v_e_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec_ref(v_info_915_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_923_, lean_object* v_e_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_923_, v_e_924_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_933_, lean_object* v_e_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_933_, v_e_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec_ref(v_info_933_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_945_ = l_Lean_Expr_isConstOf(v_e_943_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_946_);
lean_dec_ref(v_e_946_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_982_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_Expr_cleanupAnnotations(v_e_982_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_985_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Expr_isApp(v___x_983_);
if (v___x_986_ == 0)
{
lean_dec_ref(v___x_983_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_983_);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_989_ = l_Lean_Expr_isConstOf(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_987_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
v___x_996_ = l_Lean_Expr_isApp(v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v___x_995_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_995_);
v___x_998_ = l_Lean_Expr_isApp(v___x_997_);
if (v___x_998_ == 0)
{
lean_dec_ref(v___x_997_);
return v___x_998_;
}
else
{
lean_object* v_arg_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_arg_999_ = lean_ctor_get(v___x_997_, 1);
lean_inc_ref(v_arg_999_);
v___x_1000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_997_);
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1002_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1006_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1008_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1010_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1009_);
lean_dec_ref(v___x_1000_);
if (v___x_1010_ == 0)
{
lean_dec_ref(v_arg_999_);
return v___x_1010_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_999_);
lean_dec_ref(v_arg_999_);
return v___x_1011_;
}
}
else
{
uint8_t v___x_1012_; 
lean_dec_ref(v___x_1000_);
v___x_1012_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_999_);
lean_dec_ref(v_arg_999_);
return v___x_1012_;
}
}
else
{
uint8_t v___x_1013_; 
lean_dec_ref(v___x_1000_);
v___x_1013_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_999_);
lean_dec_ref(v_arg_999_);
return v___x_1013_;
}
}
else
{
uint8_t v___x_1014_; 
lean_dec_ref(v___x_1000_);
v___x_1014_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_999_);
lean_dec_ref(v_arg_999_);
return v___x_1014_;
}
}
else
{
uint8_t v___x_1015_; 
lean_dec_ref(v___x_1000_);
v___x_1015_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_999_);
lean_dec_ref(v_arg_999_);
return v___x_1015_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_987_);
return v___x_989_;
}
}
}
else
{
lean_dec_ref(v___x_983_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1016_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1025_, lean_object* v_inst_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
lean_inc_ref(v_inst_1026_);
lean_inc_ref(v_e_1025_);
v___x_1034_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1025_, v_inst_1026_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1085_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1085_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1085_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_unbox(v_a_1035_);
lean_dec(v_a_1035_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_del_object(v___x_1037_);
v___x_1040_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1027_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1073_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1073_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1073_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
uint8_t v_verbose_1045_; 
v_verbose_1045_ = lean_ctor_get_uint8(v_a_1041_, 0);
lean_dec(v_a_1041_);
if (v_verbose_1045_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_inst_1026_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_e_1025_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_e_1025_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_del_object(v___x_1043_);
v___x_1049_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1025_);
v___x_1050_ = l_Lean_indentExpr(v_e_1025_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_indentExpr(v_inst_1026_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_Meta_Sym_reportIssue(v___x_1055_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1056_, 0);
lean_dec(v_unused_1064_);
v___x_1058_ = v___x_1056_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_e_1025_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_e_1025_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_e_1025_);
v_a_1065_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1056_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1056_);
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
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_e_1025_);
v_a_1074_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1040_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1040_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v___x_1083_; 
lean_dec_ref(v_e_1025_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_inst_1026_);
v___x_1083_ = v___x_1037_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_inst_1026_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_e_1025_);
v_a_1086_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1034_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1034_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1094_, lean_object* v_inst_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1094_, v_inst_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1107_, lean_object* v_type_1108_, uint8_t v_report_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
lean_inc_ref(v_type_1108_);
v___x_1117_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1108_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1169_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1169_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1169_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
if (lean_obj_tag(v_a_1118_) == 1)
{
lean_object* v_val_1122_; lean_object* v___x_1123_; 
lean_del_object(v___x_1120_);
lean_dec_ref(v_type_1108_);
v_val_1122_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_val_1122_);
lean_dec_ref_known(v_a_1118_, 1);
v___x_1123_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1107_, v_val_1122_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1123_;
}
else
{
lean_dec(v_a_1118_);
if (v_report_1109_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_type_1108_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_e_1107_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_e_1107_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
else
{
lean_object* v___x_1127_; 
lean_del_object(v___x_1120_);
v___x_1127_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1110_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1160_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1160_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1160_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v_verbose_1132_; 
v_verbose_1132_ = lean_ctor_get_uint8(v_a_1128_, 0);
lean_dec(v_a_1128_);
if (v_verbose_1132_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_type_1108_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_e_1107_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_e_1107_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_del_object(v___x_1130_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1107_);
v___x_1137_ = l_Lean_indentExpr(v_e_1107_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_indentExpr(v_type_1108_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_Meta_Sym_reportIssue(v___x_1142_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1143_, 0);
lean_dec(v_unused_1151_);
v___x_1145_ = v___x_1143_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v___x_1143_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_e_1107_);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_e_1107_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_e_1107_);
v_a_1152_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1143_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1143_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_type_1108_);
lean_dec_ref(v_e_1107_);
v_a_1161_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1127_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1127_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_type_1108_);
lean_dec_ref(v_e_1107_);
v_a_1170_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1117_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1117_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1178_, lean_object* v_type_1179_, lean_object* v_report_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
uint8_t v_report_boxed_1188_; lean_object* v_res_1189_; 
v_report_boxed_1188_ = lean_unbox(v_report_1180_);
v_res_1189_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1178_, v_type_1179_, v_report_boxed_1188_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1190_, lean_object* v_type_1191_, uint8_t v_report_1192_, uint8_t v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1190_, v_type_1191_, v_report_1192_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1202_, lean_object* v_type_1203_, lean_object* v_report_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v_report_boxed_1213_; uint8_t v_a_boxed_1214_; lean_object* v_res_1215_; 
v_report_boxed_1213_ = lean_unbox(v_report_1204_);
v_a_boxed_1214_ = lean_unbox(v_a_1205_);
v_res_1215_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1202_, v_type_1203_, v_report_boxed_1213_, v_a_boxed_1214_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1216_, lean_object* v_x_1217_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = 0;
return v___x_1218_;
}
else
{
lean_object* v_key_1219_; lean_object* v_tail_1220_; uint8_t v___x_1221_; 
v_key_1219_ = lean_ctor_get(v_x_1217_, 0);
v_tail_1220_ = lean_ctor_get(v_x_1217_, 2);
v___x_1221_ = lean_expr_eqv(v_key_1219_, v_a_1216_);
if (v___x_1221_ == 0)
{
v_x_1217_ = v_tail_1220_;
goto _start;
}
else
{
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1223_, lean_object* v_x_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1223_, v_x_1224_);
lean_dec(v_x_1224_);
lean_dec_ref(v_a_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
return v_x_1227_;
}
else
{
lean_object* v_key_1229_; lean_object* v_value_1230_; lean_object* v_tail_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1254_; 
v_key_1229_ = lean_ctor_get(v_x_1228_, 0);
v_value_1230_ = lean_ctor_get(v_x_1228_, 1);
v_tail_1231_ = lean_ctor_get(v_x_1228_, 2);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1233_ = v_x_1228_;
v_isShared_1234_ = v_isSharedCheck_1254_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_tail_1231_);
lean_inc(v_value_1230_);
lean_inc(v_key_1229_);
lean_dec(v_x_1228_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1254_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; uint64_t v_fold_1239_; uint64_t v___x_1240_; uint64_t v___x_1241_; uint64_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1235_ = lean_array_get_size(v_x_1227_);
v___x_1236_ = l_Lean_Expr_hash(v_key_1229_);
v___x_1237_ = 32ULL;
v___x_1238_ = lean_uint64_shift_right(v___x_1236_, v___x_1237_);
v_fold_1239_ = lean_uint64_xor(v___x_1236_, v___x_1238_);
v___x_1240_ = 16ULL;
v___x_1241_ = lean_uint64_shift_right(v_fold_1239_, v___x_1240_);
v___x_1242_ = lean_uint64_xor(v_fold_1239_, v___x_1241_);
v___x_1243_ = lean_uint64_to_usize(v___x_1242_);
v___x_1244_ = lean_usize_of_nat(v___x_1235_);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_sub(v___x_1244_, v___x_1245_);
v___x_1247_ = lean_usize_land(v___x_1243_, v___x_1246_);
v___x_1248_ = lean_array_uget_borrowed(v_x_1227_, v___x_1247_);
lean_inc(v___x_1248_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 2, v___x_1248_);
v___x_1250_ = v___x_1233_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_key_1229_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_value_1230_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_array_uset(v_x_1227_, v___x_1247_, v___x_1250_);
v_x_1227_ = v___x_1251_;
v_x_1228_ = v_tail_1231_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object* v_i_1255_, lean_object* v_source_1256_, lean_object* v_target_1257_){
_start:
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = lean_array_get_size(v_source_1256_);
v___x_1259_ = lean_nat_dec_lt(v_i_1255_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec_ref(v_source_1256_);
lean_dec(v_i_1255_);
return v_target_1257_;
}
else
{
lean_object* v_es_1260_; lean_object* v___x_1261_; lean_object* v_source_1262_; lean_object* v_target_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_es_1260_ = lean_array_fget(v_source_1256_, v_i_1255_);
v___x_1261_ = lean_box(0);
v_source_1262_ = lean_array_fset(v_source_1256_, v_i_1255_, v___x_1261_);
v_target_1263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_target_1257_, v_es_1260_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_i_1255_, v___x_1264_);
lean_dec(v_i_1255_);
v_i_1255_ = v___x_1265_;
v_source_1256_ = v_source_1262_;
v_target_1257_ = v_target_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_nbuckets_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1268_ = lean_array_get_size(v_data_1267_);
v___x_1269_ = lean_unsigned_to_nat(2u);
v_nbuckets_1270_ = lean_nat_mul(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_mk_array(v_nbuckets_1270_, v___x_1272_);
v___x_1274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v___x_1271_, v_data_1267_, v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1275_, lean_object* v_b_1276_, lean_object* v_x_1277_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_dec(v_b_1276_);
lean_dec_ref(v_a_1275_);
return v_x_1277_;
}
else
{
lean_object* v_key_1278_; lean_object* v_value_1279_; lean_object* v_tail_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1292_; 
v_key_1278_ = lean_ctor_get(v_x_1277_, 0);
v_value_1279_ = lean_ctor_get(v_x_1277_, 1);
v_tail_1280_ = lean_ctor_get(v_x_1277_, 2);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1277_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1282_ = v_x_1277_;
v_isShared_1283_ = v_isSharedCheck_1292_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_tail_1280_);
lean_inc(v_value_1279_);
lean_inc(v_key_1278_);
lean_dec(v_x_1277_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1292_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_expr_eqv(v_key_1278_, v_a_1275_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1275_, v_b_1276_, v_tail_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 2, v___x_1285_);
v___x_1287_ = v___x_1282_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_key_1278_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_value_1279_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v___x_1290_; 
lean_dec(v_value_1279_);
lean_dec(v_key_1278_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v_b_1276_);
lean_ctor_set(v___x_1282_, 0, v_a_1275_);
v___x_1290_ = v___x_1282_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_b_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_tail_1280_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1293_, lean_object* v_a_1294_, lean_object* v_b_1295_){
_start:
{
lean_object* v_size_1296_; lean_object* v_buckets_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1340_; 
v_size_1296_ = lean_ctor_get(v_m_1293_, 0);
v_buckets_1297_ = lean_ctor_get(v_m_1293_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_m_1293_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1299_ = v_m_1293_;
v_isShared_1300_ = v_isSharedCheck_1340_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_buckets_1297_);
lean_inc(v_size_1296_);
lean_dec(v_m_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1340_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; uint64_t v___x_1302_; uint64_t v___x_1303_; uint64_t v___x_1304_; uint64_t v_fold_1305_; uint64_t v___x_1306_; uint64_t v___x_1307_; uint64_t v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; lean_object* v_bkt_1314_; uint8_t v___x_1315_; 
v___x_1301_ = lean_array_get_size(v_buckets_1297_);
v___x_1302_ = l_Lean_Expr_hash(v_a_1294_);
v___x_1303_ = 32ULL;
v___x_1304_ = lean_uint64_shift_right(v___x_1302_, v___x_1303_);
v_fold_1305_ = lean_uint64_xor(v___x_1302_, v___x_1304_);
v___x_1306_ = 16ULL;
v___x_1307_ = lean_uint64_shift_right(v_fold_1305_, v___x_1306_);
v___x_1308_ = lean_uint64_xor(v_fold_1305_, v___x_1307_);
v___x_1309_ = lean_uint64_to_usize(v___x_1308_);
v___x_1310_ = lean_usize_of_nat(v___x_1301_);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_sub(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_usize_land(v___x_1309_, v___x_1312_);
v_bkt_1314_ = lean_array_uget_borrowed(v_buckets_1297_, v___x_1313_);
v___x_1315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1294_, v_bkt_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v_size_x27_1317_; lean_object* v___x_1318_; lean_object* v_buckets_x27_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v_size_x27_1317_ = lean_nat_add(v_size_1296_, v___x_1316_);
lean_dec(v_size_1296_);
lean_inc(v_bkt_1314_);
v___x_1318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1294_);
lean_ctor_set(v___x_1318_, 1, v_b_1295_);
lean_ctor_set(v___x_1318_, 2, v_bkt_1314_);
v_buckets_x27_1319_ = lean_array_uset(v_buckets_1297_, v___x_1313_, v___x_1318_);
v___x_1320_ = lean_unsigned_to_nat(4u);
v___x_1321_ = lean_nat_mul(v_size_x27_1317_, v___x_1320_);
v___x_1322_ = lean_unsigned_to_nat(3u);
v___x_1323_ = lean_nat_div(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_array_get_size(v_buckets_x27_1319_);
v___x_1325_ = lean_nat_dec_le(v___x_1323_, v___x_1324_);
lean_dec(v___x_1323_);
if (v___x_1325_ == 0)
{
lean_object* v_val_1326_; lean_object* v___x_1328_; 
v_val_1326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1319_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v_val_1326_);
lean_ctor_set(v___x_1299_, 0, v_size_x27_1317_);
v___x_1328_ = v___x_1299_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_size_x27_1317_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_val_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
else
{
lean_object* v___x_1331_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v_buckets_x27_1319_);
lean_ctor_set(v___x_1299_, 0, v_size_x27_1317_);
v___x_1331_ = v___x_1299_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_size_x27_1317_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_buckets_x27_1319_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v_buckets_x27_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_inc(v_bkt_1314_);
v___x_1333_ = lean_box(0);
v_buckets_x27_1334_ = lean_array_uset(v_buckets_1297_, v___x_1313_, v___x_1333_);
v___x_1335_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1294_, v_b_1295_, v_bkt_1314_);
v___x_1336_ = lean_array_uset(v_buckets_x27_1334_, v___x_1313_, v___x_1335_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1336_);
v___x_1338_ = v___x_1299_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_size_1296_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object* v_k_1341_, uint8_t v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_box(v___y_1342_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
v___x_1352_ = lean_apply_9(v_k_1341_, v_b_1345_, v___x_1351_, v___y_1343_, v___y_1344_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, lean_box(0));
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object* v_k_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v___y_61306__boxed_1363_; lean_object* v_res_1364_; 
v___y_61306__boxed_1363_ = lean_unbox(v___y_1354_);
v_res_1364_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1353_, v___y_61306__boxed_1363_, v___y_1355_, v___y_1356_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object* v_name_1365_, uint8_t v_bi_1366_, lean_object* v_type_1367_, lean_object* v_k_1368_, uint8_t v_kind_1369_, uint8_t v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_box(v___y_1370_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
v___f_1379_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1379_, 0, v_k_1368_);
lean_closure_set(v___f_1379_, 1, v___x_1378_);
lean_closure_set(v___f_1379_, 2, v___y_1371_);
lean_closure_set(v___f_1379_, 3, v___y_1372_);
v___x_1380_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1365_, v_bi_1366_, v_type_1367_, v___f_1379_, v_kind_1369_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1380_) == 0)
{
return v___x_1380_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object* v_name_1389_, lean_object* v_bi_1390_, lean_object* v_type_1391_, lean_object* v_k_1392_, lean_object* v_kind_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_bi_boxed_1402_; uint8_t v_kind_boxed_1403_; uint8_t v___y_61334__boxed_1404_; lean_object* v_res_1405_; 
v_bi_boxed_1402_ = lean_unbox(v_bi_1390_);
v_kind_boxed_1403_ = lean_unbox(v_kind_1393_);
v___y_61334__boxed_1404_ = lean_unbox(v___y_1394_);
v_res_1405_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1389_, v_bi_boxed_1402_, v_type_1391_, v_k_1392_, v_kind_boxed_1403_, v___y_61334__boxed_1404_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_env_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1409_ = lean_st_ref_get(v___y_1407_);
v_env_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_env_1410_);
lean_dec(v___x_1409_);
v___x_1411_ = l_Lean_Meta_isMatcherCore(v_env_1410_, v_declName_1406_);
v___x_1412_ = lean_box(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1414_, v___y_1415_);
lean_dec(v___y_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v_env_1425_; lean_object* v___x_1426_; lean_object* v_toCold_1427_; lean_object* v_mctx_1428_; lean_object* v_lctx_1429_; lean_object* v_options_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1424_ = lean_st_ref_get(v___y_1422_);
v_env_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc_ref(v_env_1425_);
lean_dec(v___x_1424_);
v___x_1426_ = lean_st_ref_get(v___y_1420_);
v_toCold_1427_ = lean_ctor_get(v___y_1421_, 0);
v_mctx_1428_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_ref(v_mctx_1428_);
lean_dec(v___x_1426_);
v_lctx_1429_ = lean_ctor_get(v___y_1419_, 2);
v_options_1430_ = lean_ctor_get(v_toCold_1427_, 2);
lean_inc_ref(v_options_1430_);
lean_inc_ref(v_lctx_1429_);
v___x_1431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1431_, 0, v_env_1425_);
lean_ctor_set(v___x_1431_, 1, v_mctx_1428_);
lean_ctor_set(v___x_1431_, 2, v_lctx_1429_);
lean_ctor_set(v___x_1431_, 3, v_options_1430_);
v___x_1432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_msgData_1418_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1440_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1441_; double v___x_1442_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_float_of_nat(v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1499_; 
v_ref_1453_ = lean_ctor_get(v___y_1450_, 2);
v___x_1454_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1499_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1499_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v_traceState_1460_; lean_object* v_env_1461_; lean_object* v_nextMacroScope_1462_; lean_object* v_ngen_1463_; lean_object* v_auxDeclNGen_1464_; lean_object* v_cache_1465_; lean_object* v_messages_1466_; lean_object* v_infoState_1467_; lean_object* v_snapshotTasks_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1498_; 
v___x_1459_ = lean_st_ref_take(v___y_1451_);
v_traceState_1460_ = lean_ctor_get(v___x_1459_, 4);
v_env_1461_ = lean_ctor_get(v___x_1459_, 0);
v_nextMacroScope_1462_ = lean_ctor_get(v___x_1459_, 1);
v_ngen_1463_ = lean_ctor_get(v___x_1459_, 2);
v_auxDeclNGen_1464_ = lean_ctor_get(v___x_1459_, 3);
v_cache_1465_ = lean_ctor_get(v___x_1459_, 5);
v_messages_1466_ = lean_ctor_get(v___x_1459_, 6);
v_infoState_1467_ = lean_ctor_get(v___x_1459_, 7);
v_snapshotTasks_1468_ = lean_ctor_get(v___x_1459_, 8);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1470_ = v___x_1459_;
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snapshotTasks_1468_);
lean_inc(v_infoState_1467_);
lean_inc(v_messages_1466_);
lean_inc(v_cache_1465_);
lean_inc(v_traceState_1460_);
lean_inc(v_auxDeclNGen_1464_);
lean_inc(v_ngen_1463_);
lean_inc(v_nextMacroScope_1462_);
lean_inc(v_env_1461_);
lean_dec(v___x_1459_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
uint64_t v_tid_1472_; lean_object* v_traces_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1497_; 
v_tid_1472_ = lean_ctor_get_uint64(v_traceState_1460_, sizeof(void*)*1);
v_traces_1473_ = lean_ctor_get(v_traceState_1460_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_traceState_1460_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1475_ = v_traceState_1460_;
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_traces_1473_);
lean_dec(v_traceState_1460_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; double v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1479_ = 0;
v___x_1480_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1481_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1481_, 0, v_cls_1446_);
lean_ctor_set(v___x_1481_, 1, v___x_1477_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
lean_ctor_set_float(v___x_1481_, sizeof(void*)*3, v___x_1478_);
lean_ctor_set_float(v___x_1481_, sizeof(void*)*3 + 8, v___x_1478_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3 + 16, v___x_1479_);
v___x_1482_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1483_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v_a_1455_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
lean_inc(v_ref_1453_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_ref_1453_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_PersistentArray_push___redArg(v_traces_1473_, v___x_1484_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1485_);
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1485_);
lean_ctor_set_uint64(v_reuseFailAlloc_1496_, sizeof(void*)*1, v_tid_1472_);
v___x_1487_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___x_1487_);
v___x_1489_ = v___x_1470_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_env_1461_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_nextMacroScope_1462_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_ngen_1463_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_auxDeclNGen_1464_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v_cache_1465_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_messages_1466_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_infoState_1467_);
lean_ctor_set(v_reuseFailAlloc_1495_, 8, v_snapshotTasks_1468_);
v___x_1489_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_st_ref_put(v___y_1451_, v___x_1489_);
v___x_1491_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1491_);
v___x_1493_ = v___x_1457_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1500_, v_msg_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1508_, lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_box(0);
return v___x_1510_;
}
else
{
lean_object* v_key_1511_; lean_object* v_value_1512_; lean_object* v_tail_1513_; uint8_t v___x_1514_; 
v_key_1511_ = lean_ctor_get(v_x_1509_, 0);
v_value_1512_ = lean_ctor_get(v_x_1509_, 1);
v_tail_1513_ = lean_ctor_get(v_x_1509_, 2);
v___x_1514_ = lean_expr_eqv(v_key_1511_, v_a_1508_);
if (v___x_1514_ == 0)
{
v_x_1509_ = v_tail_1513_;
goto _start;
}
else
{
lean_object* v___x_1516_; 
lean_inc(v_value_1512_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_value_1512_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1517_, v_x_1518_);
lean_dec(v_x_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_buckets_1522_; lean_object* v___x_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; uint64_t v___x_1526_; uint64_t v_fold_1527_; uint64_t v___x_1528_; uint64_t v___x_1529_; uint64_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; size_t v___x_1534_; size_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_buckets_1522_ = lean_ctor_get(v_m_1520_, 1);
v___x_1523_ = lean_array_get_size(v_buckets_1522_);
v___x_1524_ = l_Lean_Expr_hash(v_a_1521_);
v___x_1525_ = 32ULL;
v___x_1526_ = lean_uint64_shift_right(v___x_1524_, v___x_1525_);
v_fold_1527_ = lean_uint64_xor(v___x_1524_, v___x_1526_);
v___x_1528_ = 16ULL;
v___x_1529_ = lean_uint64_shift_right(v_fold_1527_, v___x_1528_);
v___x_1530_ = lean_uint64_xor(v_fold_1527_, v___x_1529_);
v___x_1531_ = lean_uint64_to_usize(v___x_1530_);
v___x_1532_ = lean_usize_of_nat(v___x_1523_);
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_sub(v___x_1532_, v___x_1533_);
v___x_1535_ = lean_usize_land(v___x_1531_, v___x_1534_);
v___x_1536_ = lean_array_uget_borrowed(v_buckets_1522_, v___x_1535_);
v___x_1537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1521_, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1538_, v_a_1539_);
lean_dec_ref(v_a_1539_);
lean_dec_ref(v_m_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v_env_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = lean_st_ref_get(v___y_1542_);
v_env_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_env_1545_);
lean_dec(v___x_1544_);
v___x_1546_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1545_, v_declName_1541_);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1548_, v___y_1549_);
lean_dec(v___y_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object* v_name_1552_, lean_object* v_type_1553_, lean_object* v_val_1554_, lean_object* v_k_1555_, uint8_t v_nondep_1556_, uint8_t v_kind_1557_, uint8_t v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_box(v___y_1558_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1567_, 0, v_k_1555_);
lean_closure_set(v___f_1567_, 1, v___x_1566_);
lean_closure_set(v___f_1567_, 2, v___y_1559_);
lean_closure_set(v___f_1567_, 3, v___y_1560_);
v___x_1568_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1552_, v_type_1553_, v_val_1554_, v___f_1567_, v_nondep_1556_, v_kind_1557_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
return v___x_1568_;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object* v_name_1577_, lean_object* v_type_1578_, lean_object* v_val_1579_, lean_object* v_k_1580_, lean_object* v_nondep_1581_, lean_object* v_kind_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_nondep_boxed_1591_; uint8_t v_kind_boxed_1592_; uint8_t v___y_61581__boxed_1593_; lean_object* v_res_1594_; 
v_nondep_boxed_1591_ = lean_unbox(v_nondep_1581_);
v_kind_boxed_1592_ = lean_unbox(v_kind_1582_);
v___y_61581__boxed_1593_ = lean_unbox(v___y_1583_);
v_res_1594_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1577_, v_type_1578_, v_val_1579_, v_k_1580_, v_nondep_boxed_1591_, v_kind_boxed_1592_, v___y_61581__boxed_1593_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Lean_instInhabitedExpr;
v___x_1597_ = lean_panic_fn_borrowed(v___x_1596_, v_msg_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1600_, lean_object* v_body_1601_, lean_object* v_x_1602_, uint8_t v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_array_push(v_fvars_1600_, v_x_1602_);
v___x_1612_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1611_, v_body_1601_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1613_, lean_object* v_body_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___y_61761__boxed_1624_; lean_object* v_res_1625_; 
v___y_61761__boxed_1624_ = lean_unbox(v___y_1616_);
v_res_1625_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1613_, v_body_1614_, v_x_1615_, v___y_61761__boxed_1624_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1626_, lean_object* v_e_1627_, uint8_t v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
if (lean_obj_tag(v_e_1627_) == 6)
{
lean_object* v_binderName_1636_; lean_object* v_binderType_1637_; lean_object* v_body_1638_; uint8_t v_binderInfo_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_binderName_1636_ = lean_ctor_get(v_e_1627_, 0);
lean_inc(v_binderName_1636_);
v_binderType_1637_ = lean_ctor_get(v_e_1627_, 1);
lean_inc_ref(v_binderType_1637_);
v_body_1638_ = lean_ctor_get(v_e_1627_, 2);
lean_inc_ref(v_body_1638_);
v_binderInfo_1639_ = lean_ctor_get_uint8(v_e_1627_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1627_, 3);
v___x_1640_ = lean_expr_instantiate_rev(v_binderType_1637_, v_fvars_1626_);
lean_dec_ref(v_binderType_1637_);
v___x_1641_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1640_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___f_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1643_, 0, v_fvars_1626_);
lean_closure_set(v___f_1643_, 1, v_body_1638_);
v___x_1644_ = 0;
v___x_1645_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_1636_, v_binderInfo_1639_, v_a_1642_, v___f_1643_, v___x_1644_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
return v___x_1645_;
}
else
{
lean_dec_ref(v_body_1638_);
lean_dec(v_binderName_1636_);
lean_dec_ref(v_fvars_1626_);
return v___x_1641_;
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_expr_instantiate_rev(v_e_1627_, v_fvars_1626_);
lean_dec_ref(v_e_1627_);
v___x_1647_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1646_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; uint8_t v___x_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = 0;
v___x_1650_ = 1;
v___x_1651_ = 1;
v___x_1652_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1626_, v_a_1648_, v___x_1649_, v___x_1650_, v___x_1649_, v___x_1650_, v___x_1651_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec_ref(v_fvars_1626_);
return v___x_1652_;
}
else
{
lean_dec_ref(v_fvars_1626_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1653_, uint8_t v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
if (v_a_1654_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1663_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1662_, v_e_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1665_ = l_Lean_Meta_Sym_etaReduce(v_e_1653_);
lean_dec_ref(v_e_1653_);
v___x_1666_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1664_, v___x_1665_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1667_, lean_object* v_body_1668_, lean_object* v_x_1669_, uint8_t v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_array_push(v_fvars_1667_, v_x_1669_);
v___x_1679_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1678_, v_body_1668_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1680_, lean_object* v_body_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___y_61772__boxed_1691_; lean_object* v_res_1692_; 
v___y_61772__boxed_1691_ = lean_unbox(v___y_1683_);
v_res_1692_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1680_, v_body_1681_, v_x_1682_, v___y_61772__boxed_1691_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1693_, lean_object* v_e_1694_, uint8_t v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
if (lean_obj_tag(v_e_1694_) == 8)
{
lean_object* v_declName_1703_; lean_object* v_type_1704_; lean_object* v_value_1705_; lean_object* v_body_1706_; uint8_t v_nondep_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_declName_1703_ = lean_ctor_get(v_e_1694_, 0);
lean_inc(v_declName_1703_);
v_type_1704_ = lean_ctor_get(v_e_1694_, 1);
lean_inc_ref(v_type_1704_);
v_value_1705_ = lean_ctor_get(v_e_1694_, 2);
lean_inc_ref(v_value_1705_);
v_body_1706_ = lean_ctor_get(v_e_1694_, 3);
lean_inc_ref(v_body_1706_);
v_nondep_1707_ = lean_ctor_get_uint8(v_e_1694_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1694_, 4);
v___x_1708_ = lean_expr_instantiate_rev(v_type_1704_, v_fvars_1693_);
lean_dec_ref(v_type_1704_);
v___x_1709_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1708_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = lean_expr_instantiate_rev(v_value_1705_, v_fvars_1693_);
lean_dec_ref(v_value_1705_);
v___x_1712_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1711_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___f_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___f_1714_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1714_, 0, v_fvars_1693_);
lean_closure_set(v___f_1714_, 1, v_body_1706_);
v___x_1715_ = 0;
v___x_1716_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_declName_1703_, v_a_1710_, v_a_1713_, v___f_1714_, v_nondep_1707_, v___x_1715_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1716_;
}
else
{
lean_dec(v_a_1710_);
lean_dec_ref(v_body_1706_);
lean_dec(v_declName_1703_);
lean_dec_ref(v_fvars_1693_);
return v___x_1712_;
}
}
else
{
lean_dec_ref(v_body_1706_);
lean_dec_ref(v_value_1705_);
lean_dec(v_declName_1703_);
lean_dec_ref(v_fvars_1693_);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_expr_instantiate_rev(v_e_1694_, v_fvars_1693_);
lean_dec_ref(v_e_1694_);
v___x_1718_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1717_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = 1;
v___x_1721_ = 0;
v___x_1722_ = 1;
v___x_1723_ = l_Lean_Meta_mkLetFVars(v_fvars_1693_, v_a_1719_, v___x_1720_, v___x_1721_, v___x_1722_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec_ref(v_fvars_1693_);
return v___x_1723_;
}
else
{
lean_dec_ref(v_fvars_1693_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1724_, uint8_t v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
if (v_a_1725_ == 0)
{
uint8_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = 1;
v___x_1734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1724_, v___x_1733_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1736_, uint8_t v_report_1737_, uint8_t v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
lean_inc(v_a_1744_);
lean_inc_ref(v_a_1743_);
lean_inc(v_a_1742_);
lean_inc_ref(v_a_1741_);
lean_inc_ref(v_e_1736_);
v___x_1746_ = lean_infer_type(v_e_1736_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_n(v_a_1747_, 2);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = l_Lean_Meta_isProp(v_a_1747_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1761_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (v_a_1738_ == 0)
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
if (v___x_1757_ == 0)
{
lean_del_object(v___x_1751_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1759_; 
lean_dec(v_a_1747_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v_e_1736_);
v___x_1759_ = v___x_1751_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_e_1736_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
lean_del_object(v___x_1751_);
lean_dec(v_a_1749_);
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1747_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1736_, v_a_1755_, v_report_1737_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1756_;
}
else
{
lean_dec_ref(v_e_1736_);
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1747_);
lean_dec_ref(v_e_1736_);
v_a_1762_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1748_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1748_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_dec_ref(v_e_1736_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1770_, uint8_t v_report_1771_, uint8_t v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
if (v_a_1772_ == 0)
{
lean_object* v___x_1780_; lean_object* v_canon_1781_; lean_object* v_cache_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_st_ref_get(v_a_1774_);
v_canon_1781_ = lean_ctor_get(v___x_1780_, 9);
lean_inc_ref(v_canon_1781_);
lean_dec(v___x_1780_);
v_cache_1782_ = lean_ctor_get(v_canon_1781_, 0);
lean_inc_ref(v_cache_1782_);
lean_dec_ref(v_canon_1781_);
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1782_, v_e_1770_);
lean_dec_ref(v_cache_1782_);
if (lean_obj_tag(v___x_1783_) == 1)
{
lean_object* v_val_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_e_1770_);
v_val_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_val_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_val_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1783_);
lean_inc_ref(v_e_1770_);
v___x_1792_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1770_, v_report_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1831_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1831_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1831_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v_canon_1798_; lean_object* v_share_1799_; lean_object* v_maxFVar_1800_; lean_object* v_proofInstInfo_1801_; lean_object* v_inferType_1802_; lean_object* v_getLevel_1803_; lean_object* v_congrInfo_1804_; lean_object* v_defEqI_1805_; lean_object* v_extensions_1806_; lean_object* v_issues_1807_; lean_object* v_instanceOverrides_1808_; uint8_t v_debug_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1830_; 
v___x_1797_ = lean_st_ref_take(v_a_1774_);
v_canon_1798_ = lean_ctor_get(v___x_1797_, 9);
v_share_1799_ = lean_ctor_get(v___x_1797_, 0);
v_maxFVar_1800_ = lean_ctor_get(v___x_1797_, 1);
v_proofInstInfo_1801_ = lean_ctor_get(v___x_1797_, 2);
v_inferType_1802_ = lean_ctor_get(v___x_1797_, 3);
v_getLevel_1803_ = lean_ctor_get(v___x_1797_, 4);
v_congrInfo_1804_ = lean_ctor_get(v___x_1797_, 5);
v_defEqI_1805_ = lean_ctor_get(v___x_1797_, 6);
v_extensions_1806_ = lean_ctor_get(v___x_1797_, 7);
v_issues_1807_ = lean_ctor_get(v___x_1797_, 8);
v_instanceOverrides_1808_ = lean_ctor_get(v___x_1797_, 10);
v_debug_1809_ = lean_ctor_get_uint8(v___x_1797_, sizeof(void*)*11);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1811_ = v___x_1797_;
v_isShared_1812_ = v_isSharedCheck_1830_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_instanceOverrides_1808_);
lean_inc(v_canon_1798_);
lean_inc(v_issues_1807_);
lean_inc(v_extensions_1806_);
lean_inc(v_defEqI_1805_);
lean_inc(v_congrInfo_1804_);
lean_inc(v_getLevel_1803_);
lean_inc(v_inferType_1802_);
lean_inc(v_proofInstInfo_1801_);
lean_inc(v_maxFVar_1800_);
lean_inc(v_share_1799_);
lean_dec(v___x_1797_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1830_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_cache_1813_; lean_object* v_cacheInType_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1829_; 
v_cache_1813_ = lean_ctor_get(v_canon_1798_, 0);
v_cacheInType_1814_ = lean_ctor_get(v_canon_1798_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_canon_1798_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1816_ = v_canon_1798_;
v_isShared_1817_ = v_isSharedCheck_1829_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_cacheInType_1814_);
lean_inc(v_cache_1813_);
lean_dec(v_canon_1798_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1829_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_inc(v_a_1793_);
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1813_, v_e_1770_, v_a_1793_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_cacheInType_1814_);
v___x_1820_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 9, v___x_1820_);
v___x_1822_ = v___x_1811_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_share_1799_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_maxFVar_1800_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_proofInstInfo_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_inferType_1802_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_getLevel_1803_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_congrInfo_1804_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_defEqI_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_extensions_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_issues_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 9, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1827_, 10, v_instanceOverrides_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*11, v_debug_1809_);
v___x_1822_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_st_ref_put(v_a_1774_, v___x_1822_);
if (v_isShared_1796_ == 0)
{
v___x_1825_ = v___x_1795_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1793_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1770_);
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v_canon_1833_; lean_object* v_cacheInType_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_st_ref_get(v_a_1774_);
v_canon_1833_ = lean_ctor_get(v___x_1832_, 9);
lean_inc_ref(v_canon_1833_);
lean_dec(v___x_1832_);
v_cacheInType_1834_ = lean_ctor_get(v_canon_1833_, 1);
lean_inc_ref(v_cacheInType_1834_);
lean_dec_ref(v_canon_1833_);
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1834_, v_e_1770_);
lean_dec_ref(v_cacheInType_1834_);
if (lean_obj_tag(v___x_1835_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_e_1770_);
v_val_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 0);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_val_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v___x_1844_; 
lean_dec(v___x_1835_);
lean_inc_ref(v_e_1770_);
v___x_1844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1770_, v_report_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1883_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1883_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1883_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v_canon_1850_; lean_object* v_share_1851_; lean_object* v_maxFVar_1852_; lean_object* v_proofInstInfo_1853_; lean_object* v_inferType_1854_; lean_object* v_getLevel_1855_; lean_object* v_congrInfo_1856_; lean_object* v_defEqI_1857_; lean_object* v_extensions_1858_; lean_object* v_issues_1859_; lean_object* v_instanceOverrides_1860_; uint8_t v_debug_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1882_; 
v___x_1849_ = lean_st_ref_take(v_a_1774_);
v_canon_1850_ = lean_ctor_get(v___x_1849_, 9);
v_share_1851_ = lean_ctor_get(v___x_1849_, 0);
v_maxFVar_1852_ = lean_ctor_get(v___x_1849_, 1);
v_proofInstInfo_1853_ = lean_ctor_get(v___x_1849_, 2);
v_inferType_1854_ = lean_ctor_get(v___x_1849_, 3);
v_getLevel_1855_ = lean_ctor_get(v___x_1849_, 4);
v_congrInfo_1856_ = lean_ctor_get(v___x_1849_, 5);
v_defEqI_1857_ = lean_ctor_get(v___x_1849_, 6);
v_extensions_1858_ = lean_ctor_get(v___x_1849_, 7);
v_issues_1859_ = lean_ctor_get(v___x_1849_, 8);
v_instanceOverrides_1860_ = lean_ctor_get(v___x_1849_, 10);
v_debug_1861_ = lean_ctor_get_uint8(v___x_1849_, sizeof(void*)*11);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1863_ = v___x_1849_;
v_isShared_1864_ = v_isSharedCheck_1882_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_instanceOverrides_1860_);
lean_inc(v_canon_1850_);
lean_inc(v_issues_1859_);
lean_inc(v_extensions_1858_);
lean_inc(v_defEqI_1857_);
lean_inc(v_congrInfo_1856_);
lean_inc(v_getLevel_1855_);
lean_inc(v_inferType_1854_);
lean_inc(v_proofInstInfo_1853_);
lean_inc(v_maxFVar_1852_);
lean_inc(v_share_1851_);
lean_dec(v___x_1849_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1882_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_cache_1865_; lean_object* v_cacheInType_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1881_; 
v_cache_1865_ = lean_ctor_get(v_canon_1850_, 0);
v_cacheInType_1866_ = lean_ctor_get(v_canon_1850_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_canon_1850_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1868_ = v_canon_1850_;
v_isShared_1869_ = v_isSharedCheck_1881_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_cacheInType_1866_);
lean_inc(v_cache_1865_);
lean_dec(v_canon_1850_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1881_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_inc(v_a_1845_);
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1866_, v_e_1770_, v_a_1845_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_cache_1865_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 9, v___x_1872_);
v___x_1874_ = v___x_1863_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_share_1851_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_maxFVar_1852_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_proofInstInfo_1853_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_inferType_1854_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_getLevel_1855_);
lean_ctor_set(v_reuseFailAlloc_1879_, 5, v_congrInfo_1856_);
lean_ctor_set(v_reuseFailAlloc_1879_, 6, v_defEqI_1857_);
lean_ctor_set(v_reuseFailAlloc_1879_, 7, v_extensions_1858_);
lean_ctor_set(v_reuseFailAlloc_1879_, 8, v_issues_1859_);
lean_ctor_set(v_reuseFailAlloc_1879_, 9, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1879_, 10, v_instanceOverrides_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*11, v_debug_1861_);
v___x_1874_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = lean_st_ref_put(v_a_1774_, v___x_1874_);
if (v_isShared_1848_ == 0)
{
v___x_1877_ = v___x_1847_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1845_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1770_);
return v___x_1844_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1900_ = l_Lean_mkConst(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1901_, lean_object* v_prop_1902_, lean_object* v_inst_1903_, lean_object* v_e_1904_, uint8_t v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
lean_inc_ref(v_prop_1902_);
v___x_1913_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1902_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1956_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1956_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1956_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___y_1919_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1914_);
v___x_1925_ = l_Lean_Expr_app___override(v___x_1924_, v_a_1914_);
if (v_a_1905_ == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1925_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___y_1929_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
if (lean_obj_tag(v_a_1927_) == 0)
{
lean_inc_ref(v_inst_1903_);
v___y_1929_ = v_inst_1903_;
goto v___jp_1928_;
}
else
{
lean_object* v_val_1945_; 
v_val_1945_ = lean_ctor_get(v_a_1927_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v_a_1927_, 1);
v___y_1929_ = v_val_1945_;
goto v___jp_1928_;
}
v___jp_1928_:
{
lean_object* v___x_1930_; 
lean_inc_ref(v_inst_1903_);
v___x_1930_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1903_, v___y_1929_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1944_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1944_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1944_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
size_t v___x_1935_; size_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_ptr_addr(v_prop_1902_);
lean_dec_ref(v_prop_1902_);
v___x_1936_ = lean_ptr_addr(v_a_1914_);
v___x_1937_ = lean_usize_dec_eq(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_del_object(v___x_1933_);
lean_dec_ref(v_e_1904_);
lean_dec_ref(v_inst_1903_);
v___y_1919_ = v_a_1931_;
goto v___jp_1918_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = lean_ptr_addr(v_inst_1903_);
lean_dec_ref(v_inst_1903_);
v___x_1939_ = lean_ptr_addr(v_a_1931_);
v___x_1940_ = lean_usize_dec_eq(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_del_object(v___x_1933_);
lean_dec_ref(v_e_1904_);
v___y_1919_ = v_a_1931_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1942_; 
lean_dec(v_a_1931_);
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
lean_dec_ref(v_g_1901_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v_e_1904_);
v___x_1942_ = v___x_1933_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_e_1904_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
lean_dec_ref(v_e_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v_prop_1902_);
lean_dec_ref(v_g_1901_);
return v___x_1930_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
lean_dec_ref(v_e_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v_prop_1902_);
lean_dec_ref(v_g_1901_);
v_a_1946_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1926_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1926_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
uint8_t v___x_1954_; lean_object* v___x_1955_; 
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
lean_dec_ref(v_e_1904_);
lean_dec_ref(v_prop_1902_);
lean_dec_ref(v_g_1901_);
v___x_1954_ = 0;
v___x_1955_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1903_, v___x_1925_, v___x_1954_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1955_;
}
v___jp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = l_Lean_mkAppB(v_g_1901_, v_a_1914_, v___y_1919_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1920_);
v___x_1922_ = v___x_1916_;
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
else
{
lean_dec_ref(v_e_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v_prop_1902_);
lean_dec_ref(v_g_1901_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1957_, lean_object* v_prop_1958_, lean_object* v_h_1959_, lean_object* v_e_1960_, uint8_t v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
if (v_a_1961_ == 0)
{
lean_object* v___x_1969_; lean_object* v_canon_1970_; lean_object* v_cache_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_st_ref_get(v_a_1963_);
v_canon_1970_ = lean_ctor_get(v___x_1969_, 9);
lean_inc_ref(v_canon_1970_);
lean_dec(v___x_1969_);
v_cache_1971_ = lean_ctor_get(v_canon_1970_, 0);
lean_inc_ref(v_cache_1971_);
lean_dec_ref(v_canon_1970_);
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1971_, v_e_1960_);
lean_dec_ref(v_cache_1971_);
if (lean_obj_tag(v___x_1972_) == 1)
{
lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_e_1960_);
lean_dec_ref(v_h_1959_);
lean_dec_ref(v_prop_1958_);
lean_dec_ref(v_g_1957_);
v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 0);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_val_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v___x_1972_);
lean_inc_ref(v_e_1960_);
v___x_1981_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1957_, v_prop_1958_, v_h_1959_, v_e_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2020_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2020_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2020_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v_canon_1987_; lean_object* v_share_1988_; lean_object* v_maxFVar_1989_; lean_object* v_proofInstInfo_1990_; lean_object* v_inferType_1991_; lean_object* v_getLevel_1992_; lean_object* v_congrInfo_1993_; lean_object* v_defEqI_1994_; lean_object* v_extensions_1995_; lean_object* v_issues_1996_; lean_object* v_instanceOverrides_1997_; uint8_t v_debug_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2019_; 
v___x_1986_ = lean_st_ref_take(v_a_1963_);
v_canon_1987_ = lean_ctor_get(v___x_1986_, 9);
v_share_1988_ = lean_ctor_get(v___x_1986_, 0);
v_maxFVar_1989_ = lean_ctor_get(v___x_1986_, 1);
v_proofInstInfo_1990_ = lean_ctor_get(v___x_1986_, 2);
v_inferType_1991_ = lean_ctor_get(v___x_1986_, 3);
v_getLevel_1992_ = lean_ctor_get(v___x_1986_, 4);
v_congrInfo_1993_ = lean_ctor_get(v___x_1986_, 5);
v_defEqI_1994_ = lean_ctor_get(v___x_1986_, 6);
v_extensions_1995_ = lean_ctor_get(v___x_1986_, 7);
v_issues_1996_ = lean_ctor_get(v___x_1986_, 8);
v_instanceOverrides_1997_ = lean_ctor_get(v___x_1986_, 10);
v_debug_1998_ = lean_ctor_get_uint8(v___x_1986_, sizeof(void*)*11);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2000_ = v___x_1986_;
v_isShared_2001_ = v_isSharedCheck_2019_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_instanceOverrides_1997_);
lean_inc(v_canon_1987_);
lean_inc(v_issues_1996_);
lean_inc(v_extensions_1995_);
lean_inc(v_defEqI_1994_);
lean_inc(v_congrInfo_1993_);
lean_inc(v_getLevel_1992_);
lean_inc(v_inferType_1991_);
lean_inc(v_proofInstInfo_1990_);
lean_inc(v_maxFVar_1989_);
lean_inc(v_share_1988_);
lean_dec(v___x_1986_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2019_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_cache_2002_; lean_object* v_cacheInType_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2018_; 
v_cache_2002_ = lean_ctor_get(v_canon_1987_, 0);
v_cacheInType_2003_ = lean_ctor_get(v_canon_1987_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_canon_1987_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2005_ = v_canon_1987_;
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_cacheInType_2003_);
lean_inc(v_cache_2002_);
lean_dec(v_canon_1987_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_inc(v_a_1982_);
v___x_2007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2002_, v_e_1960_, v_a_1982_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_cacheInType_2003_);
v___x_2009_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 9, v___x_2009_);
v___x_2011_ = v___x_2000_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_share_1988_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_maxFVar_1989_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_proofInstInfo_1990_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_inferType_1991_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_getLevel_1992_);
lean_ctor_set(v_reuseFailAlloc_2016_, 5, v_congrInfo_1993_);
lean_ctor_set(v_reuseFailAlloc_2016_, 6, v_defEqI_1994_);
lean_ctor_set(v_reuseFailAlloc_2016_, 7, v_extensions_1995_);
lean_ctor_set(v_reuseFailAlloc_2016_, 8, v_issues_1996_);
lean_ctor_set(v_reuseFailAlloc_2016_, 9, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2016_, 10, v_instanceOverrides_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*11, v_debug_1998_);
v___x_2011_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_st_ref_put(v_a_1963_, v___x_2011_);
if (v_isShared_1985_ == 0)
{
v___x_2014_ = v___x_1984_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_1982_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1960_);
return v___x_1981_;
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v_canon_2022_; lean_object* v_cacheInType_2023_; lean_object* v___x_2024_; 
v___x_2021_ = lean_st_ref_get(v_a_1963_);
v_canon_2022_ = lean_ctor_get(v___x_2021_, 9);
lean_inc_ref(v_canon_2022_);
lean_dec(v___x_2021_);
v_cacheInType_2023_ = lean_ctor_get(v_canon_2022_, 1);
lean_inc_ref(v_cacheInType_2023_);
lean_dec_ref(v_canon_2022_);
v___x_2024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2023_, v_e_1960_);
lean_dec_ref(v_cacheInType_2023_);
if (lean_obj_tag(v___x_2024_) == 1)
{
lean_object* v_val_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_e_1960_);
lean_dec_ref(v_h_1959_);
lean_dec_ref(v_prop_1958_);
lean_dec_ref(v_g_1957_);
v_val_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_val_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 0);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_val_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec(v___x_2024_);
lean_inc_ref(v_e_1960_);
v___x_2033_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1957_, v_prop_1958_, v_h_1959_, v_e_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2072_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2072_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2072_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v_canon_2039_; lean_object* v_share_2040_; lean_object* v_maxFVar_2041_; lean_object* v_proofInstInfo_2042_; lean_object* v_inferType_2043_; lean_object* v_getLevel_2044_; lean_object* v_congrInfo_2045_; lean_object* v_defEqI_2046_; lean_object* v_extensions_2047_; lean_object* v_issues_2048_; lean_object* v_instanceOverrides_2049_; uint8_t v_debug_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2071_; 
v___x_2038_ = lean_st_ref_take(v_a_1963_);
v_canon_2039_ = lean_ctor_get(v___x_2038_, 9);
v_share_2040_ = lean_ctor_get(v___x_2038_, 0);
v_maxFVar_2041_ = lean_ctor_get(v___x_2038_, 1);
v_proofInstInfo_2042_ = lean_ctor_get(v___x_2038_, 2);
v_inferType_2043_ = lean_ctor_get(v___x_2038_, 3);
v_getLevel_2044_ = lean_ctor_get(v___x_2038_, 4);
v_congrInfo_2045_ = lean_ctor_get(v___x_2038_, 5);
v_defEqI_2046_ = lean_ctor_get(v___x_2038_, 6);
v_extensions_2047_ = lean_ctor_get(v___x_2038_, 7);
v_issues_2048_ = lean_ctor_get(v___x_2038_, 8);
v_instanceOverrides_2049_ = lean_ctor_get(v___x_2038_, 10);
v_debug_2050_ = lean_ctor_get_uint8(v___x_2038_, sizeof(void*)*11);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2052_ = v___x_2038_;
v_isShared_2053_ = v_isSharedCheck_2071_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_instanceOverrides_2049_);
lean_inc(v_canon_2039_);
lean_inc(v_issues_2048_);
lean_inc(v_extensions_2047_);
lean_inc(v_defEqI_2046_);
lean_inc(v_congrInfo_2045_);
lean_inc(v_getLevel_2044_);
lean_inc(v_inferType_2043_);
lean_inc(v_proofInstInfo_2042_);
lean_inc(v_maxFVar_2041_);
lean_inc(v_share_2040_);
lean_dec(v___x_2038_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2071_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_cache_2054_; lean_object* v_cacheInType_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2070_; 
v_cache_2054_ = lean_ctor_get(v_canon_2039_, 0);
v_cacheInType_2055_ = lean_ctor_get(v_canon_2039_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_canon_2039_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2057_ = v_canon_2039_;
v_isShared_2058_ = v_isSharedCheck_2070_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_cacheInType_2055_);
lean_inc(v_cache_2054_);
lean_dec(v_canon_2039_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2070_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_inc(v_a_2034_);
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2055_, v_e_1960_, v_a_2034_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_cache_2054_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 9, v___x_2061_);
v___x_2063_ = v___x_2052_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_share_2040_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_maxFVar_2041_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_proofInstInfo_2042_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_inferType_2043_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_getLevel_2044_);
lean_ctor_set(v_reuseFailAlloc_2068_, 5, v_congrInfo_2045_);
lean_ctor_set(v_reuseFailAlloc_2068_, 6, v_defEqI_2046_);
lean_ctor_set(v_reuseFailAlloc_2068_, 7, v_extensions_2047_);
lean_ctor_set(v_reuseFailAlloc_2068_, 8, v_issues_2048_);
lean_ctor_set(v_reuseFailAlloc_2068_, 9, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2068_, 10, v_instanceOverrides_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*11, v_debug_2050_);
v___x_2063_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_st_ref_put(v_a_1963_, v___x_2063_);
if (v_isShared_2037_ == 0)
{
v___x_2066_ = v___x_2036_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2034_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1960_);
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2073_, lean_object* v_prop_2074_, lean_object* v_h_2075_, lean_object* v_e_2076_, uint8_t v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_a_2086_; lean_object* v___y_2120_; 
if (v_a_2077_ == 0)
{
lean_object* v___x_2160_; lean_object* v_canon_2161_; lean_object* v_cache_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_st_ref_get(v_a_2079_);
v_canon_2161_ = lean_ctor_get(v___x_2160_, 9);
lean_inc_ref(v_canon_2161_);
lean_dec(v___x_2160_);
v_cache_2162_ = lean_ctor_get(v_canon_2161_, 0);
lean_inc_ref(v_cache_2162_);
lean_dec_ref(v_canon_2161_);
v___x_2163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2162_, v_e_2076_);
lean_dec_ref(v_cache_2162_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_e_2076_);
lean_dec_ref(v_h_2075_);
lean_dec_ref(v_prop_2074_);
lean_dec_ref(v_g_2073_);
v_val_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 0);
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_val_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v___x_2172_; 
lean_dec(v___x_2163_);
lean_inc_ref(v_prop_2074_);
v___x_2172_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2074_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_n(v_a_2173_, 2);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2173_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___y_2177_; lean_object* v___y_2180_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
if (lean_obj_tag(v_a_2175_) == 0)
{
lean_inc_ref(v_h_2075_);
v___y_2180_ = v_h_2075_;
goto v___jp_2179_;
}
else
{
lean_object* v_val_2187_; 
v_val_2187_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v_a_2175_, 1);
v___y_2180_ = v_val_2187_;
goto v___jp_2179_;
}
v___jp_2176_:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_mkAppB(v_g_2073_, v_a_2173_, v___y_2177_);
v_a_2086_ = v___x_2178_;
goto v___jp_2085_;
}
v___jp_2179_:
{
size_t v___x_2181_; size_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = lean_ptr_addr(v_prop_2074_);
lean_dec_ref(v_prop_2074_);
v___x_2182_ = lean_ptr_addr(v_a_2173_);
v___x_2183_ = lean_usize_dec_eq(v___x_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_dec_ref(v_h_2075_);
v___y_2177_ = v___y_2180_;
goto v___jp_2176_;
}
else
{
size_t v___x_2184_; size_t v___x_2185_; uint8_t v___x_2186_; 
v___x_2184_ = lean_ptr_addr(v_h_2075_);
lean_dec_ref(v_h_2075_);
v___x_2185_ = lean_ptr_addr(v___y_2180_);
v___x_2186_ = lean_usize_dec_eq(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
v___y_2177_ = v___y_2180_;
goto v___jp_2176_;
}
else
{
lean_dec_ref(v___y_2180_);
lean_dec(v_a_2173_);
lean_dec_ref(v_g_2073_);
lean_inc_ref(v_e_2076_);
v_a_2086_ = v_e_2076_;
goto v___jp_2085_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2173_);
lean_dec_ref(v_e_2076_);
lean_dec_ref(v_h_2075_);
lean_dec_ref(v_prop_2074_);
lean_dec_ref(v_g_2073_);
v_a_2188_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2174_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2174_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_dec_ref(v_h_2075_);
lean_dec_ref(v_prop_2074_);
lean_dec_ref(v_g_2073_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2172_, 1);
v_a_2086_ = v_a_2196_;
goto v___jp_2085_;
}
else
{
lean_dec_ref(v_e_2076_);
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v_canon_2198_; lean_object* v_cacheInType_2199_; lean_object* v___x_2200_; 
lean_dec_ref(v_g_2073_);
v___x_2197_ = lean_st_ref_get(v_a_2079_);
v_canon_2198_ = lean_ctor_get(v___x_2197_, 9);
lean_inc_ref(v_canon_2198_);
lean_dec(v___x_2197_);
v_cacheInType_2199_ = lean_ctor_get(v_canon_2198_, 1);
lean_inc_ref(v_cacheInType_2199_);
lean_dec_ref(v_canon_2198_);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2199_, v_e_2076_);
lean_dec_ref(v_cacheInType_2199_);
if (lean_obj_tag(v___x_2200_) == 1)
{
lean_object* v_val_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_e_2076_);
lean_dec_ref(v_h_2075_);
lean_dec_ref(v_prop_2074_);
v_val_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_val_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 0);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_val_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v___x_2209_; 
lean_dec(v___x_2200_);
v___x_2209_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2074_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = 0;
v___x_2212_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2075_, v_a_2210_, v___x_2211_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
v___y_2120_ = v___x_2212_;
goto v___jp_2119_;
}
else
{
lean_dec_ref(v_h_2075_);
v___y_2120_ = v___x_2209_;
goto v___jp_2119_;
}
}
}
v___jp_2085_:
{
lean_object* v___x_2087_; lean_object* v_canon_2088_; lean_object* v_share_2089_; lean_object* v_maxFVar_2090_; lean_object* v_proofInstInfo_2091_; lean_object* v_inferType_2092_; lean_object* v_getLevel_2093_; lean_object* v_congrInfo_2094_; lean_object* v_defEqI_2095_; lean_object* v_extensions_2096_; lean_object* v_issues_2097_; lean_object* v_instanceOverrides_2098_; uint8_t v_debug_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2118_; 
v___x_2087_ = lean_st_ref_take(v_a_2079_);
v_canon_2088_ = lean_ctor_get(v___x_2087_, 9);
v_share_2089_ = lean_ctor_get(v___x_2087_, 0);
v_maxFVar_2090_ = lean_ctor_get(v___x_2087_, 1);
v_proofInstInfo_2091_ = lean_ctor_get(v___x_2087_, 2);
v_inferType_2092_ = lean_ctor_get(v___x_2087_, 3);
v_getLevel_2093_ = lean_ctor_get(v___x_2087_, 4);
v_congrInfo_2094_ = lean_ctor_get(v___x_2087_, 5);
v_defEqI_2095_ = lean_ctor_get(v___x_2087_, 6);
v_extensions_2096_ = lean_ctor_get(v___x_2087_, 7);
v_issues_2097_ = lean_ctor_get(v___x_2087_, 8);
v_instanceOverrides_2098_ = lean_ctor_get(v___x_2087_, 10);
v_debug_2099_ = lean_ctor_get_uint8(v___x_2087_, sizeof(void*)*11);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2101_ = v___x_2087_;
v_isShared_2102_ = v_isSharedCheck_2118_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_instanceOverrides_2098_);
lean_inc(v_canon_2088_);
lean_inc(v_issues_2097_);
lean_inc(v_extensions_2096_);
lean_inc(v_defEqI_2095_);
lean_inc(v_congrInfo_2094_);
lean_inc(v_getLevel_2093_);
lean_inc(v_inferType_2092_);
lean_inc(v_proofInstInfo_2091_);
lean_inc(v_maxFVar_2090_);
lean_inc(v_share_2089_);
lean_dec(v___x_2087_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2118_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_cache_2103_; lean_object* v_cacheInType_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2117_; 
v_cache_2103_ = lean_ctor_get(v_canon_2088_, 0);
v_cacheInType_2104_ = lean_ctor_get(v_canon_2088_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_canon_2088_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2106_ = v_canon_2088_;
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_cacheInType_2104_);
lean_inc(v_cache_2103_);
lean_dec(v_canon_2088_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_inc_ref(v_a_2086_);
v___x_2108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2103_, v_e_2076_, v_a_2086_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_cacheInType_2104_);
v___x_2110_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 9, v___x_2110_);
v___x_2112_ = v___x_2101_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_share_2089_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_maxFVar_2090_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_proofInstInfo_2091_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_inferType_2092_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_getLevel_2093_);
lean_ctor_set(v_reuseFailAlloc_2115_, 5, v_congrInfo_2094_);
lean_ctor_set(v_reuseFailAlloc_2115_, 6, v_defEqI_2095_);
lean_ctor_set(v_reuseFailAlloc_2115_, 7, v_extensions_2096_);
lean_ctor_set(v_reuseFailAlloc_2115_, 8, v_issues_2097_);
lean_ctor_set(v_reuseFailAlloc_2115_, 9, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2115_, 10, v_instanceOverrides_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2115_, sizeof(void*)*11, v_debug_2099_);
v___x_2112_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_st_ref_put(v_a_2079_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_a_2086_);
return v___x_2114_;
}
}
}
}
}
v___jp_2119_:
{
if (lean_obj_tag(v___y_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2159_; 
v_a_2121_ = lean_ctor_get(v___y_2120_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___y_2120_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2123_ = v___y_2120_;
v_isShared_2124_ = v_isSharedCheck_2159_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___y_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2159_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v_canon_2126_; lean_object* v_share_2127_; lean_object* v_maxFVar_2128_; lean_object* v_proofInstInfo_2129_; lean_object* v_inferType_2130_; lean_object* v_getLevel_2131_; lean_object* v_congrInfo_2132_; lean_object* v_defEqI_2133_; lean_object* v_extensions_2134_; lean_object* v_issues_2135_; lean_object* v_instanceOverrides_2136_; uint8_t v_debug_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2158_; 
v___x_2125_ = lean_st_ref_take(v_a_2079_);
v_canon_2126_ = lean_ctor_get(v___x_2125_, 9);
v_share_2127_ = lean_ctor_get(v___x_2125_, 0);
v_maxFVar_2128_ = lean_ctor_get(v___x_2125_, 1);
v_proofInstInfo_2129_ = lean_ctor_get(v___x_2125_, 2);
v_inferType_2130_ = lean_ctor_get(v___x_2125_, 3);
v_getLevel_2131_ = lean_ctor_get(v___x_2125_, 4);
v_congrInfo_2132_ = lean_ctor_get(v___x_2125_, 5);
v_defEqI_2133_ = lean_ctor_get(v___x_2125_, 6);
v_extensions_2134_ = lean_ctor_get(v___x_2125_, 7);
v_issues_2135_ = lean_ctor_get(v___x_2125_, 8);
v_instanceOverrides_2136_ = lean_ctor_get(v___x_2125_, 10);
v_debug_2137_ = lean_ctor_get_uint8(v___x_2125_, sizeof(void*)*11);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2139_ = v___x_2125_;
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_instanceOverrides_2136_);
lean_inc(v_canon_2126_);
lean_inc(v_issues_2135_);
lean_inc(v_extensions_2134_);
lean_inc(v_defEqI_2133_);
lean_inc(v_congrInfo_2132_);
lean_inc(v_getLevel_2131_);
lean_inc(v_inferType_2130_);
lean_inc(v_proofInstInfo_2129_);
lean_inc(v_maxFVar_2128_);
lean_inc(v_share_2127_);
lean_dec(v___x_2125_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_cache_2141_; lean_object* v_cacheInType_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2157_; 
v_cache_2141_ = lean_ctor_get(v_canon_2126_, 0);
v_cacheInType_2142_ = lean_ctor_get(v_canon_2126_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_canon_2126_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2144_ = v_canon_2126_;
v_isShared_2145_ = v_isSharedCheck_2157_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_cacheInType_2142_);
lean_inc(v_cache_2141_);
lean_dec(v_canon_2126_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2157_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_inc(v_a_2121_);
v___x_2146_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2142_, v_e_2076_, v_a_2121_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_cache_2141_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 9, v___x_2148_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_share_2127_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_maxFVar_2128_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_proofInstInfo_2129_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_inferType_2130_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_getLevel_2131_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_congrInfo_2132_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_defEqI_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_extensions_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v_issues_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 9, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 10, v_instanceOverrides_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*11, v_debug_2137_);
v___x_2150_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_st_ref_put(v_a_2079_, v___x_2150_);
if (v_isShared_2124_ == 0)
{
v___x_2153_ = v___x_2123_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2121_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2076_);
return v___y_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2213_, lean_object* v_a_2214_, lean_object* v___x_2215_, lean_object* v_snd_2216_, uint8_t v___x_2217_, lean_object* v_fst_2218_, lean_object* v_____r_2219_, uint8_t v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_arg_x27_2229_; lean_object* v___x_2241_; 
lean_inc_ref(v___x_2215_);
v___x_2241_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2213_, v_a_2214_, v___x_2215_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; uint8_t v___x_2243_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2243_ = lean_unbox(v_a_2242_);
lean_dec(v_a_2242_);
switch(v___x_2243_)
{
case 0:
{
lean_object* v___x_2244_; 
lean_inc_ref(v___x_2215_);
v___x_2244_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2215_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v_arg_x27_2229_ = v_a_2245_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2246_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2244_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2244_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
case 1:
{
lean_object* v___x_2254_; 
lean_inc_ref(v___x_2215_);
v___x_2254_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2215_, v___y_2224_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; uint8_t v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2274_ = l_Lean_Expr_cleanupAnnotations(v_a_2255_);
v___x_2275_ = l_Lean_Expr_isApp(v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec_ref(v___x_2274_);
v___y_2257_ = v___y_2220_;
v___y_2258_ = v___y_2221_;
v___y_2259_ = v___y_2222_;
v___y_2260_ = v___y_2223_;
v___y_2261_ = v___y_2224_;
v___y_2262_ = v___y_2225_;
v___y_2263_ = v___y_2226_;
goto v___jp_2256_;
}
else
{
lean_object* v_arg_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_arg_2276_ = lean_ctor_get(v___x_2274_, 1);
lean_inc_ref(v_arg_2276_);
v___x_2277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2274_);
v___x_2278_ = l_Lean_Expr_isApp(v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v___x_2277_);
lean_dec_ref(v_arg_2276_);
v___y_2257_ = v___y_2220_;
v___y_2258_ = v___y_2221_;
v___y_2259_ = v___y_2222_;
v___y_2260_ = v___y_2223_;
v___y_2261_ = v___y_2224_;
v___y_2262_ = v___y_2225_;
v___y_2263_ = v___y_2226_;
goto v___jp_2256_;
}
else
{
lean_object* v_arg_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_arg_2279_ = lean_ctor_get(v___x_2277_, 1);
lean_inc_ref(v_arg_2279_);
v___x_2280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2277_);
v___x_2281_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2282_ = l_Lean_Expr_isConstOf(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2284_ = l_Lean_Expr_isConstOf(v___x_2280_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2280_);
lean_dec_ref(v_arg_2279_);
lean_dec_ref(v_arg_2276_);
v___y_2257_ = v___y_2220_;
v___y_2258_ = v___y_2221_;
v___y_2259_ = v___y_2222_;
v___y_2260_ = v___y_2223_;
v___y_2261_ = v___y_2224_;
v___y_2262_ = v___y_2225_;
v___y_2263_ = v___y_2226_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2285_; 
lean_inc_ref(v___x_2215_);
v___x_2285_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2280_, v_arg_2279_, v_arg_2276_, v___x_2215_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v_arg_x27_2229_ = v_a_2286_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2287_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2285_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2285_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
else
{
lean_object* v___x_2295_; 
lean_inc_ref(v___x_2215_);
v___x_2295_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2280_, v_arg_2279_, v_arg_2276_, v___x_2215_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v_arg_x27_2229_ = v_a_2296_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2297_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
}
v___jp_2256_:
{
lean_object* v___x_2264_; 
lean_inc_ref(v___x_2215_);
v___x_2264_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2215_, v___x_2217_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_arg_x27_2229_ = v_a_2265_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2266_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2264_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2264_);
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
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2305_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2254_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2254_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
default: 
{
lean_object* v___x_2313_; 
lean_inc_ref(v___x_2215_);
v___x_2313_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2215_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v_arg_x27_2229_ = v_a_2314_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2315_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2313_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_fst_2218_);
lean_dec(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_a_2323_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2241_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2241_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
v___jp_2228_:
{
size_t v___x_2230_; size_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2230_ = lean_ptr_addr(v___x_2215_);
lean_dec_ref(v___x_2215_);
v___x_2231_ = lean_ptr_addr(v_arg_x27_2229_);
v___x_2232_ = lean_usize_dec_eq(v___x_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v_fst_2218_);
v___x_2233_ = lean_array_fset(v_snd_2216_, v_a_2214_, v_arg_x27_2229_);
v___x_2234_ = lean_box(v___x_2217_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2233_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_arg_x27_2229_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_fst_2218_);
lean_ctor_set(v___x_2238_, 1, v_snd_2216_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2335_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2336_ = l_Lean_Name_append(v___x_2335_, v___x_2334_);
return v___x_2336_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2346_, lean_object* v___x_2347_, lean_object* v_a_2348_, lean_object* v_b_2349_, uint8_t v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___y_2359_; uint8_t v___x_2381_; 
v___x_2381_ = lean_nat_dec_lt(v_a_2348_, v_upperBound_2346_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_dec(v_a_2348_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_b_2349_);
return v___x_2382_;
}
else
{
lean_object* v_toCold_2383_; lean_object* v_options_2384_; lean_object* v_fst_2385_; lean_object* v_snd_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2450_; 
v_toCold_2383_ = lean_ctor_get(v___y_2355_, 0);
v_options_2384_ = lean_ctor_get(v_toCold_2383_, 2);
v_fst_2385_ = lean_ctor_get(v_b_2349_, 0);
v_snd_2386_ = lean_ctor_get(v_b_2349_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_b_2349_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2388_ = v_b_2349_;
v_isShared_2389_ = v_isSharedCheck_2450_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snd_2386_);
lean_inc(v_fst_2385_);
lean_dec(v_b_2349_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2450_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_inheritedTraceOptions_2390_; uint8_t v_hasTrace_2391_; lean_object* v___x_2392_; 
v_inheritedTraceOptions_2390_ = lean_ctor_get(v_toCold_2383_, 11);
v_hasTrace_2391_ = lean_ctor_get_uint8(v_options_2384_, sizeof(void*)*1);
v___x_2392_ = lean_array_fget(v_snd_2386_, v_a_2348_);
if (v_hasTrace_2391_ == 0)
{
lean_del_object(v___x_2388_);
goto v___jp_2393_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2397_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2398_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2390_, v_options_2384_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_del_object(v___x_2388_);
goto v___jp_2393_;
}
else
{
lean_object* v___x_2399_; 
lean_inc(v___x_2392_);
v___x_2399_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2347_, v_a_2348_, v___x_2392_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
lean_inc(v___y_2356_);
lean_inc_ref(v___y_2355_);
lean_inc(v___y_2354_);
lean_inc_ref(v___y_2353_);
lean_inc(v___x_2392_);
v___x_2401_ = lean_infer_type(v___x_2392_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; lean_object* v___y_2405_; uint8_t v___x_2429_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2403_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2429_ = lean_unbox(v_a_2400_);
lean_dec(v_a_2400_);
switch(v___x_2429_)
{
case 0:
{
lean_object* v___x_2430_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2405_ = v___x_2430_;
goto v___jp_2404_;
}
case 1:
{
lean_object* v___x_2431_; 
v___x_2431_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2405_ = v___x_2431_;
goto v___jp_2404_;
}
case 2:
{
lean_object* v___x_2432_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2405_ = v___x_2432_;
goto v___jp_2404_;
}
default: 
{
lean_object* v___x_2433_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2405_ = v___x_2433_;
goto v___jp_2404_;
}
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_inc(v___y_2405_);
v___x_2406_ = l_Lean_MessageData_ofFormat(v___y_2405_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 7);
lean_ctor_set(v___x_2388_, 1, v___x_2406_);
lean_ctor_set(v___x_2388_, 0, v___x_2403_);
v___x_2408_ = v___x_2388_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2409_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
lean_inc(v___x_2392_);
v___x_2411_ = l_Lean_MessageData_ofExpr(v___x_2392_);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_MessageData_ofExpr(v_a_2402_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2396_, v___x_2416_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2347_, v_a_2348_, v___x_2392_, v_snd_2386_, v___x_2381_, v_fst_2385_, v_a_2418_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
v___y_2359_ = v___x_2419_;
goto v___jp_2358_;
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v___x_2392_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_dec(v_a_2348_);
v_a_2420_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2417_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2417_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2400_);
lean_dec(v___x_2392_);
lean_del_object(v___x_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_dec(v_a_2348_);
v_a_2434_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2401_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2401_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v___x_2392_);
lean_del_object(v___x_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_dec(v_a_2348_);
v_a_2442_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2399_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2399_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
v___jp_2393_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_box(0);
v___x_2395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2347_, v_a_2348_, v___x_2392_, v_snd_2386_, v___x_2381_, v_fst_2385_, v___x_2394_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
v___y_2359_ = v___x_2395_;
goto v___jp_2358_;
}
}
}
v___jp_2358_:
{
if (lean_obj_tag(v___y_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2372_; 
v_a_2360_ = lean_ctor_get(v___y_2359_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___y_2359_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2362_ = v___y_2359_;
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___y_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
if (lean_obj_tag(v_a_2360_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; 
lean_dec(v_a_2348_);
v_a_2364_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v_a_2360_, 1);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v_a_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_del_object(v___x_2362_);
v_a_2368_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v_a_2360_, 1);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_a_2348_, v___x_2369_);
lean_dec(v_a_2348_);
v_a_2348_ = v___x_2370_;
v_b_2349_ = v_a_2368_;
goto _start;
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2348_);
v_a_2373_ = lean_ctor_get(v___y_2359_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___y_2359_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___y_2359_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___y_2359_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_x_2454_, uint8_t v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___y_2464_; uint8_t v_modified_2465_; lean_object* v_f_2466_; uint8_t v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_args_2522_; uint8_t v_modified_2523_; uint8_t v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; uint8_t v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; 
if (lean_obj_tag(v_x_2452_) == 5)
{
lean_object* v_fn_2559_; lean_object* v_arg_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_fn_2559_ = lean_ctor_get(v_x_2452_, 0);
lean_inc_ref(v_fn_2559_);
v_arg_2560_ = lean_ctor_get(v_x_2452_, 1);
lean_inc_ref(v_arg_2560_);
lean_dec_ref_known(v_x_2452_, 2);
v___x_2561_ = lean_array_set(v_x_2453_, v_x_2454_, v_arg_2560_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = lean_nat_sub(v_x_2454_, v___x_2562_);
lean_dec(v_x_2454_);
v_x_2452_ = v_fn_2559_;
v_x_2453_ = v___x_2561_;
v_x_2454_ = v___x_2563_;
goto _start;
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
lean_dec(v_x_2454_);
v___x_2565_ = lean_array_get_size(v_x_2453_);
v___x_2566_ = lean_unsigned_to_nat(2u);
v___x_2567_ = lean_nat_dec_eq(v___x_2565_, v___x_2566_);
if (v___x_2567_ == 0)
{
v___y_2538_ = v___y_2455_;
v___y_2539_ = v___y_2456_;
v___y_2540_ = v___y_2457_;
v___y_2541_ = v___y_2458_;
v___y_2542_ = v___y_2459_;
v___y_2543_ = v___y_2460_;
v___y_2544_ = v___y_2461_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = l_Lean_instInhabitedExpr;
v___x_2569_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2570_ = l_Lean_Expr_isConstOf(v_x_2452_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2572_ = l_Lean_Expr_isConstOf(v_x_2452_, v___x_2571_);
if (v___x_2572_ == 0)
{
v___y_2538_ = v___y_2455_;
v___y_2539_ = v___y_2456_;
v___y_2540_ = v___y_2457_;
v___y_2541_ = v___y_2458_;
v___y_2542_ = v___y_2459_;
v___y_2543_ = v___y_2460_;
v___y_2544_ = v___y_2461_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_array_get(v___x_2568_, v_x_2453_, v___x_2573_);
v___x_2575_ = lean_unsigned_to_nat(1u);
v___x_2576_ = lean_array_get(v___x_2568_, v_x_2453_, v___x_2575_);
lean_dec_ref(v_x_2453_);
v___x_2577_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2452_, v___x_2574_, v___x_2576_, v_e_2451_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2577_;
}
}
else
{
lean_object* v___x_2578_; lean_object* v_prop_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_unsigned_to_nat(0u);
v_prop_2579_ = lean_array_get_borrowed(v___x_2568_, v_x_2453_, v___x_2578_);
lean_inc(v_prop_2579_);
v___x_2580_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2579_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2597_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2597_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2597_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
size_t v___x_2585_; size_t v___x_2586_; uint8_t v___x_2587_; 
v___x_2585_ = lean_ptr_addr(v_prop_2579_);
v___x_2586_ = lean_ptr_addr(v_a_2581_);
v___x_2587_ = lean_usize_dec_eq(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_dec_ref(v_e_2451_);
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_array_get(v___x_2568_, v_x_2453_, v___x_2588_);
lean_dec_ref(v_x_2453_);
v___x_2590_ = l_Lean_mkAppB(v_x_2452_, v_a_2581_, v___x_2589_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2590_);
v___x_2592_ = v___x_2583_;
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
else
{
lean_object* v___x_2595_; 
lean_dec(v_a_2581_);
lean_dec_ref(v_x_2453_);
lean_dec_ref(v_x_2452_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_e_2451_);
v___x_2595_ = v___x_2583_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_e_2451_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_dec_ref(v_x_2453_);
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_e_2451_);
return v___x_2580_;
}
}
}
}
v___jp_2463_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_box(0);
lean_inc_ref(v_f_2466_);
v___x_2475_ = l_Lean_Meta_getFunInfo(v_f_2466_, v___x_2474_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v_paramInfo_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2511_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v_paramInfo_2477_ = lean_ctor_get(v_a_2476_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_a_2476_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v_a_2476_, 1);
lean_dec(v_unused_2512_);
v___x_2479_ = v_a_2476_;
v_isShared_2480_ = v_isSharedCheck_2511_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_paramInfo_2477_);
lean_dec(v_a_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2511_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2481_ = lean_array_get_size(v___y_2464_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_box(v_modified_2465_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___y_2464_);
lean_ctor_set(v___x_2479_, 0, v___x_2483_);
v___x_2485_ = v___x_2479_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___y_2464_);
v___x_2485_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2481_, v_paramInfo_2477_, v___x_2482_, v___x_2485_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec_ref(v_paramInfo_2477_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2501_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2501_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2501_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_fst_2491_; uint8_t v___x_2492_; 
v_fst_2491_ = lean_ctor_get(v_a_2487_, 0);
v___x_2492_ = lean_unbox(v_fst_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2494_; 
lean_dec(v_a_2487_);
lean_dec_ref(v_f_2466_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v_e_2451_);
v___x_2494_ = v___x_2489_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_e_2451_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
lean_object* v_snd_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_dec_ref(v_e_2451_);
v_snd_2496_ = lean_ctor_get(v_a_2487_, 1);
lean_inc(v_snd_2496_);
lean_dec(v_a_2487_);
v___x_2497_ = l_Lean_mkAppN(v_f_2466_, v_snd_2496_);
lean_dec(v_snd_2496_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2497_);
v___x_2499_ = v___x_2489_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref(v_f_2466_);
lean_dec_ref(v_e_2451_);
v_a_2502_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2486_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2486_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_f_2466_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_e_2451_);
v_a_2513_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2475_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2475_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
v___jp_2521_:
{
lean_object* v___x_2531_; 
lean_inc_ref(v_x_2452_);
v___x_2531_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2452_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; size_t v___x_2533_; size_t v___x_2534_; uint8_t v___x_2535_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = lean_ptr_addr(v_x_2452_);
v___x_2534_ = lean_ptr_addr(v_a_2532_);
v___x_2535_ = lean_usize_dec_eq(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
uint8_t v___x_2536_; 
lean_dec_ref(v_x_2452_);
v___x_2536_ = 1;
v___y_2464_ = v_args_2522_;
v_modified_2465_ = v___x_2536_;
v_f_2466_ = v_a_2532_;
v___y_2467_ = v___y_2524_;
v___y_2468_ = v___y_2525_;
v___y_2469_ = v___y_2526_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
goto v___jp_2463_;
}
else
{
lean_dec(v_a_2532_);
v___y_2464_ = v_args_2522_;
v_modified_2465_ = v_modified_2523_;
v_f_2466_ = v_x_2452_;
v___y_2467_ = v___y_2524_;
v___y_2468_ = v___y_2525_;
v___y_2469_ = v___y_2526_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
goto v___jp_2463_;
}
}
else
{
lean_dec_ref(v_args_2522_);
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_e_2451_);
return v___x_2531_;
}
}
v___jp_2537_:
{
uint8_t v_modified_2545_; lean_object* v___x_2546_; uint8_t v_modified_2547_; 
v_modified_2545_ = 0;
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2547_ = l_Lean_Expr_isConstOf(v_x_2452_, v___x_2546_);
if (v_modified_2547_ == 0)
{
v_args_2522_ = v_x_2453_;
v_modified_2523_ = v_modified_2545_;
v___y_2524_ = v___y_2538_;
v___y_2525_ = v___y_2539_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
goto v___jp_2521_;
}
else
{
lean_object* v___x_2548_; 
lean_inc_ref(v_x_2453_);
v___x_2548_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2453_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
if (lean_obj_tag(v_a_2549_) == 1)
{
lean_object* v_val_2550_; 
lean_dec_ref(v_x_2453_);
v_val_2550_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v_a_2549_, 1);
v_args_2522_ = v_val_2550_;
v_modified_2523_ = v_modified_2547_;
v___y_2524_ = v___y_2538_;
v___y_2525_ = v___y_2539_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
goto v___jp_2521_;
}
else
{
lean_dec(v_a_2549_);
v_args_2522_ = v_x_2453_;
v_modified_2523_ = v_modified_2545_;
v___y_2524_ = v___y_2538_;
v___y_2525_ = v___y_2539_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
goto v___jp_2521_;
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_x_2453_);
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_e_2451_);
v_a_2551_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2548_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2598_, uint8_t v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_dummy_2607_; lean_object* v_nargs_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_dummy_2607_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2608_ = l_Lean_Expr_getAppNumArgs(v_e_2598_);
lean_inc(v_nargs_2608_);
v___x_2609_ = lean_mk_array(v_nargs_2608_, v_dummy_2607_);
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_sub(v_nargs_2608_, v___x_2610_);
lean_dec(v_nargs_2608_);
lean_inc_ref(v_e_2598_);
v___x_2612_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2598_, v_e_2598_, v___x_2609_, v___x_2611_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2613_, uint8_t v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
uint8_t v___x_2642_; 
lean_inc_ref(v_e_2613_);
v___x_2642_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2613_);
if (v___x_2642_ == 0)
{
lean_object* v_f_2643_; 
v_f_2643_ = l_Lean_Expr_getAppFn(v_e_2613_);
if (lean_obj_tag(v_f_2643_) == 4)
{
lean_object* v_declName_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_declName_2644_ = lean_ctor_get(v_f_2643_, 0);
lean_inc(v_declName_2644_);
lean_dec_ref_known(v_f_2643_, 2);
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0));
v___x_2646_ = lean_name_eq(v_declName_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2648_ = lean_name_eq(v_declName_2644_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2650_ = lean_name_eq(v_declName_2644_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2652_ = lean_name_eq(v_declName_2644_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2644_, v_a_2620_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2683_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2683_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2683_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
if (lean_obj_tag(v_a_2654_) == 1)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; 
lean_del_object(v___x_2656_);
v_val_2658_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v_a_2654_, 1);
lean_inc_ref(v_e_2613_);
v___x_2659_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2658_, v_e_2613_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_val_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2671_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2671_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2671_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_e_2613_);
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_e_2613_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2669_; 
lean_dec_ref(v_e_2613_);
v_val_2667_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_a_2660_, 1);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_val_2667_);
v___x_2669_ = v___x_2662_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_val_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_e_2613_);
v_a_2672_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2659_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2659_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_e_2613_);
v___x_2681_ = v___x_2656_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_e_2613_);
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
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v_e_2613_);
v_a_2684_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2653_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2653_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_dec(v_declName_2644_);
goto v___jp_2622_;
}
}
else
{
lean_dec(v_declName_2644_);
goto v___jp_2622_;
}
}
else
{
lean_dec(v_declName_2644_);
goto v___jp_2622_;
}
}
else
{
lean_dec(v_declName_2644_);
goto v___jp_2622_;
}
}
else
{
lean_object* v___x_2692_; 
lean_dec_ref(v_f_2643_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_e_2613_);
return v___x_2692_;
}
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_inc_ref(v_e_2613_);
v___x_2693_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2693_, 0, v_e_2613_);
v___x_2694_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2693_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2728_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2728_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2728_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
if (lean_obj_tag(v_a_2695_) == 1)
{
lean_object* v_val_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec_ref(v_e_2613_);
v_val_2699_ = lean_ctor_get(v_a_2695_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v_a_2695_, 1);
v___x_2700_ = l_Lean_mkNatLit(v_val_2699_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
else
{
lean_object* v___x_2704_; 
lean_del_object(v___x_2697_);
lean_dec(v_a_2695_);
lean_inc_ref(v_e_2613_);
v___x_2704_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2613_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2719_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
if (lean_obj_tag(v_a_2705_) == 1)
{
lean_object* v_val_2709_; lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec_ref(v_e_2613_);
v_val_2709_ = lean_ctor_get(v_a_2705_, 0);
lean_inc(v_val_2709_);
lean_dec_ref_known(v_a_2705_, 1);
v_fst_2710_ = lean_ctor_get(v_val_2709_, 0);
lean_inc(v_fst_2710_);
v_snd_2711_ = lean_ctor_get(v_val_2709_, 1);
lean_inc(v_snd_2711_);
lean_dec(v_val_2709_);
v___x_2712_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2710_, v_snd_2711_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2712_);
v___x_2714_ = v___x_2707_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
else
{
lean_object* v___x_2717_; 
lean_dec(v_a_2705_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v_e_2613_);
v___x_2717_ = v___x_2707_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_e_2613_);
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
lean_dec_ref(v_e_2613_);
v_a_2720_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2704_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2704_);
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
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_e_2613_);
v_a_2729_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2694_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2694_);
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
v___jp_2622_:
{
lean_object* v___x_2623_; 
lean_inc_ref(v_e_2613_);
v___x_2623_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2613_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2633_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2633_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2633_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
if (lean_obj_tag(v_a_2624_) == 1)
{
lean_object* v_val_2628_; lean_object* v___x_2629_; 
lean_del_object(v___x_2626_);
lean_dec_ref(v_e_2613_);
v_val_2628_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v_a_2624_, 1);
v___x_2629_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2628_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
return v___x_2629_;
}
else
{
lean_object* v___x_2631_; 
lean_dec(v_a_2624_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v_e_2613_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_e_2613_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v_e_2613_);
v_a_2634_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2623_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2623_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2737_, uint8_t v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2747_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
return v___x_2748_;
}
else
{
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2749_, uint8_t v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2749_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
if (lean_obj_tag(v_a_2759_) == 0)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; 
lean_dec_ref(v_e_2749_);
v_val_2760_ = lean_ctor_get(v_a_2759_, 0);
lean_inc_ref(v_val_2760_);
lean_dec_ref_known(v_a_2759_, 1);
v___x_2761_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2760_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
return v___x_2761_;
}
else
{
lean_object* v___x_2762_; 
lean_dec(v_a_2759_);
v___x_2762_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2763_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2774_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2774_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2774_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
if (lean_obj_tag(v_a_2765_) == 0)
{
lean_object* v_val_2769_; lean_object* v___x_2770_; 
lean_del_object(v___x_2767_);
lean_dec(v_a_2763_);
v_val_2769_ = lean_ctor_get(v_a_2765_, 0);
lean_inc_ref(v_val_2769_);
lean_dec_ref_known(v_a_2765_, 1);
v___x_2770_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2769_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
return v___x_2770_;
}
else
{
lean_object* v___x_2772_; 
lean_dec(v_a_2765_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2763_);
v___x_2772_ = v___x_2767_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2763_);
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
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2763_);
v_a_2775_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2764_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2764_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v_e_2749_);
v_a_2783_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2758_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2758_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2797_, uint8_t v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2806_; 
lean_inc_ref(v_e_2797_);
v___x_2806_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2797_, v_a_2802_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; uint8_t v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2818_ = l_Lean_Expr_cleanupAnnotations(v_a_2807_);
v___x_2819_ = l_Lean_Expr_isApp(v___x_2818_);
if (v___x_2819_ == 0)
{
lean_dec_ref(v___x_2818_);
v___y_2809_ = v_a_2798_;
v___y_2810_ = v_a_2799_;
v___y_2811_ = v_a_2800_;
v___y_2812_ = v_a_2801_;
v___y_2813_ = v_a_2802_;
v___y_2814_ = v_a_2803_;
v___y_2815_ = v_a_2804_;
goto v___jp_2808_;
}
else
{
lean_object* v_arg_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_arg_2820_ = lean_ctor_get(v___x_2818_, 1);
lean_inc_ref(v_arg_2820_);
v___x_2821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2818_);
v___x_2822_ = l_Lean_Expr_isApp(v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_arg_2820_);
v___y_2809_ = v_a_2798_;
v___y_2810_ = v_a_2799_;
v___y_2811_ = v_a_2800_;
v___y_2812_ = v_a_2801_;
v___y_2813_ = v_a_2802_;
v___y_2814_ = v_a_2803_;
v___y_2815_ = v_a_2804_;
goto v___jp_2808_;
}
else
{
lean_object* v_arg_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_arg_2823_ = lean_ctor_get(v___x_2821_, 1);
lean_inc_ref(v_arg_2823_);
v___x_2824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2821_);
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2826_ = l_Lean_Expr_isConstOf(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_dec_ref(v___x_2824_);
lean_dec_ref(v_arg_2823_);
lean_dec_ref(v_arg_2820_);
v___y_2809_ = v_a_2798_;
v___y_2810_ = v_a_2799_;
v___y_2811_ = v_a_2800_;
v___y_2812_ = v_a_2801_;
v___y_2813_ = v_a_2802_;
v___y_2814_ = v_a_2803_;
v___y_2815_ = v_a_2804_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2827_; 
v___x_2827_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2824_, v_arg_2823_, v_arg_2820_, v_e_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
return v___x_2827_;
}
}
}
v___jp_2808_:
{
uint8_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = 0;
v___x_2817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2797_, v___x_2816_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
else
{
lean_dec_ref(v_e_2797_);
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2828_, lean_object* v_00_u03b1_2829_, lean_object* v_c_2830_, lean_object* v_inst_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_, uint8_t v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2830_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; uint8_t v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc_n(v_a_2843_, 2);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2843_);
if (v___x_2844_ == 0)
{
uint8_t v___x_2845_; 
lean_inc(v_a_2843_);
v___x_2845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2843_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
v___x_2846_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2829_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2831_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2832_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = l_Lean_mkApp5(v_f_2828_, v_a_2847_, v_a_2843_, v_a_2849_, v_a_2851_, v_a_2853_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_dec(v_a_2851_);
lean_dec(v_a_2849_);
lean_dec(v_a_2847_);
lean_dec(v_a_2843_);
lean_dec_ref(v_f_2828_);
return v___x_2852_;
}
}
else
{
lean_dec(v_a_2849_);
lean_dec(v_a_2847_);
lean_dec(v_a_2843_);
lean_dec_ref(v_b_2833_);
lean_dec_ref(v_f_2828_);
return v___x_2850_;
}
}
else
{
lean_dec(v_a_2847_);
lean_dec(v_a_2843_);
lean_dec_ref(v_b_2833_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_f_2828_);
return v___x_2848_;
}
}
else
{
lean_dec(v_a_2843_);
lean_dec_ref(v_b_2833_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_f_2828_);
return v___x_2846_;
}
}
else
{
lean_object* v___x_2862_; 
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_00_u03b1_2829_);
lean_dec_ref(v_f_2828_);
v___x_2862_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_2862_;
}
}
else
{
lean_object* v___x_2863_; 
lean_dec(v_a_2843_);
lean_dec_ref(v_b_2833_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_00_u03b1_2829_);
lean_dec_ref(v_f_2828_);
v___x_2863_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2832_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_2863_;
}
}
else
{
lean_dec_ref(v_b_2833_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_00_u03b1_2829_);
lean_dec_ref(v_f_2828_);
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2864_, lean_object* v_00_u03b1_2865_, lean_object* v_c_2866_, lean_object* v_a_2867_, lean_object* v_b_2868_, uint8_t v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2866_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; uint8_t v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc_n(v_a_2878_, 2);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = l_Lean_Expr_isBoolTrue(v_a_2878_);
if (v___x_2879_ == 0)
{
uint8_t v___x_2880_; 
lean_inc(v_a_2878_);
v___x_2880_ = l_Lean_Expr_isBoolFalse(v_a_2878_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2865_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2867_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2894_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = l_Lean_mkApp4(v_f_2864_, v_a_2882_, v_a_2878_, v_a_2884_, v_a_2886_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
lean_dec(v_a_2884_);
lean_dec(v_a_2882_);
lean_dec(v_a_2878_);
lean_dec_ref(v_f_2864_);
return v___x_2885_;
}
}
else
{
lean_dec(v_a_2882_);
lean_dec(v_a_2878_);
lean_dec_ref(v_b_2868_);
lean_dec_ref(v_f_2864_);
return v___x_2883_;
}
}
else
{
lean_dec(v_a_2878_);
lean_dec_ref(v_b_2868_);
lean_dec_ref(v_a_2867_);
lean_dec_ref(v_f_2864_);
return v___x_2881_;
}
}
else
{
lean_object* v___x_2895_; 
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2867_);
lean_dec_ref(v_00_u03b1_2865_);
lean_dec_ref(v_f_2864_);
v___x_2895_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2895_;
}
}
else
{
lean_object* v___x_2896_; 
lean_dec(v_a_2878_);
lean_dec_ref(v_b_2868_);
lean_dec_ref(v_00_u03b1_2865_);
lean_dec_ref(v_f_2864_);
v___x_2896_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2867_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2896_;
}
}
else
{
lean_dec_ref(v_b_2868_);
lean_dec_ref(v_a_2867_);
lean_dec_ref(v_00_u03b1_2865_);
lean_dec_ref(v_f_2864_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2897_, uint8_t v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; uint8_t v___y_2915_; lean_object* v___x_2933_; 
lean_inc_ref(v_e_2897_);
v___x_2933_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2897_, v_a_2902_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; uint8_t v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2945_ = l_Lean_Expr_cleanupAnnotations(v_a_2934_);
v___x_2946_ = l_Lean_Expr_isApp(v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec_ref(v___x_2945_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_arg_2947_ = lean_ctor_get(v___x_2945_, 1);
lean_inc_ref(v_arg_2947_);
v___x_2948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2945_);
v___x_2949_ = l_Lean_Expr_isApp(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_arg_2947_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v_arg_2950_ = lean_ctor_get(v___x_2948_, 1);
lean_inc_ref(v_arg_2950_);
v___x_2951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2948_);
v___x_2952_ = l_Lean_Expr_isApp(v___x_2951_);
if (v___x_2952_ == 0)
{
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_arg_2950_);
lean_dec_ref(v_arg_2947_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v_arg_2953_ = lean_ctor_get(v___x_2951_, 1);
lean_inc_ref(v_arg_2953_);
v___x_2954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2951_);
v___x_2955_ = l_Lean_Expr_isApp(v___x_2954_);
if (v___x_2955_ == 0)
{
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_arg_2953_);
lean_dec_ref(v_arg_2950_);
lean_dec_ref(v_arg_2947_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v_arg_2956_ = lean_ctor_get(v___x_2954_, 1);
lean_inc_ref(v_arg_2956_);
v___x_2957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2954_);
v___x_2958_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2959_ = l_Lean_Expr_isConstOf(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
uint8_t v___x_2960_; 
v___x_2960_ = l_Lean_Expr_isApp(v___x_2957_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_arg_2956_);
lean_dec_ref(v_arg_2953_);
lean_dec_ref(v_arg_2950_);
lean_dec_ref(v_arg_2947_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_arg_2961_ = lean_ctor_get(v___x_2957_, 1);
lean_inc_ref(v_arg_2961_);
v___x_2962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2957_);
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2964_ = l_Lean_Expr_isConstOf(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_arg_2961_);
lean_dec_ref(v_arg_2956_);
lean_dec_ref(v_arg_2953_);
lean_dec_ref(v_arg_2950_);
lean_dec_ref(v_arg_2947_);
v___y_2936_ = v_a_2898_;
v___y_2937_ = v_a_2899_;
v___y_2938_ = v_a_2900_;
v___y_2939_ = v_a_2901_;
v___y_2940_ = v_a_2902_;
v___y_2941_ = v_a_2903_;
v___y_2942_ = v_a_2904_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2965_; 
lean_dec_ref(v_e_2897_);
v___x_2965_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2962_, v_arg_2961_, v_arg_2956_, v_arg_2953_, v_arg_2950_, v_arg_2947_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2965_;
}
}
}
else
{
lean_object* v___x_2966_; 
lean_dec_ref(v_e_2897_);
v___x_2966_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2957_, v_arg_2956_, v_arg_2953_, v_arg_2950_, v_arg_2947_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2966_;
}
}
}
}
}
v___jp_2935_:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = l_Lean_Expr_getAppFn(v_e_2897_);
v___x_2944_ = l_Lean_Expr_isLambda(v___x_2943_);
if (v___x_2944_ == 0)
{
v___y_2907_ = v___y_2937_;
v___y_2908_ = v___x_2943_;
v___y_2909_ = v___y_2942_;
v___y_2910_ = v___y_2939_;
v___y_2911_ = v___y_2938_;
v___y_2912_ = v___y_2940_;
v___y_2913_ = v___y_2941_;
v___y_2914_ = v___y_2936_;
v___y_2915_ = v___x_2944_;
goto v___jp_2906_;
}
else
{
v___y_2907_ = v___y_2937_;
v___y_2908_ = v___x_2943_;
v___y_2909_ = v___y_2942_;
v___y_2910_ = v___y_2939_;
v___y_2911_ = v___y_2938_;
v___y_2912_ = v___y_2940_;
v___y_2913_ = v___y_2941_;
v___y_2914_ = v___y_2936_;
v___y_2915_ = v___y_2936_;
goto v___jp_2906_;
}
}
}
else
{
lean_dec_ref(v_e_2897_);
return v___x_2933_;
}
v___jp_2906_:
{
if (v___y_2915_ == 0)
{
if (lean_obj_tag(v___y_2908_) == 4)
{
lean_object* v_declName_2916_; lean_object* v___x_2917_; 
v_declName_2916_ = lean_ctor_get(v___y_2908_, 0);
lean_inc(v_declName_2916_);
lean_dec_ref_known(v___y_2908_, 2);
v___x_2917_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2916_, v___y_2909_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; uint8_t v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = lean_unbox(v_a_2918_);
lean_dec(v_a_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2897_, v___y_2914_, v___y_2907_, v___y_2911_, v___y_2910_, v___y_2912_, v___y_2913_, v___y_2909_);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2897_, v___y_2914_, v___y_2907_, v___y_2911_, v___y_2910_, v___y_2912_, v___y_2913_, v___y_2909_);
return v___x_2921_;
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_e_2897_);
v_a_2922_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2917_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2917_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v___x_2930_; 
lean_dec_ref(v___y_2908_);
v___x_2930_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2897_, v___y_2914_, v___y_2907_, v___y_2911_, v___y_2910_, v___y_2912_, v___y_2913_, v___y_2909_);
return v___x_2930_;
}
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref(v___y_2908_);
v___x_2931_ = l_Lean_Expr_headBeta(v_e_2897_);
v___x_2932_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2931_, v___y_2914_, v___y_2907_, v___y_2911_, v___y_2910_, v___y_2912_, v___y_2913_, v___y_2909_);
return v___x_2932_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2971_ = lean_unsigned_to_nat(18u);
v___x_2972_ = lean_unsigned_to_nat(1896u);
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2974_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2975_ = l_mkPanicMessageWithDecl(v___x_2974_, v___x_2973_, v___x_2972_, v___x_2971_, v___x_2970_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2976_, uint8_t v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = l_Lean_Expr_projExpr_x21(v_e_2976_);
v___x_2986_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2985_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___y_2989_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
if (lean_obj_tag(v_e_2976_) == 11)
{
lean_object* v_typeName_3011_; lean_object* v_idx_3012_; lean_object* v_struct_3013_; size_t v___x_3014_; size_t v___x_3015_; uint8_t v___x_3016_; 
v_typeName_3011_ = lean_ctor_get(v_e_2976_, 0);
v_idx_3012_ = lean_ctor_get(v_e_2976_, 1);
v_struct_3013_ = lean_ctor_get(v_e_2976_, 2);
v___x_3014_ = lean_ptr_addr(v_struct_3013_);
v___x_3015_ = lean_ptr_addr(v_a_2987_);
v___x_3016_ = lean_usize_dec_eq(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_inc(v_idx_3012_);
lean_inc(v_typeName_3011_);
lean_dec_ref_known(v_e_2976_, 3);
v___x_3017_ = l_Lean_Expr_proj___override(v_typeName_3011_, v_idx_3012_, v_a_2987_);
v___y_2989_ = v___x_3017_;
goto v___jp_2988_;
}
else
{
lean_dec(v_a_2987_);
v___y_2989_ = v_e_2976_;
goto v___jp_2988_;
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v_a_2987_);
lean_dec_ref(v_e_2976_);
v___x_3018_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3019_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3018_);
v___y_2989_ = v___x_3019_;
goto v___jp_2988_;
}
v___jp_2988_:
{
lean_object* v___x_2990_; 
lean_inc_ref(v___y_2989_);
v___x_2990_ = l_Lean_Meta_reduceProj_x3f(v___y_2989_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3002_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
if (lean_obj_tag(v_a_2991_) == 0)
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___y_2989_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___y_2989_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
else
{
lean_object* v_val_2998_; lean_object* v___x_3000_; 
lean_dec_ref(v___y_2989_);
v_val_2998_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_val_2998_);
lean_dec_ref_known(v_a_2991_, 1);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_val_2998_);
v___x_3000_ = v___x_2993_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_val_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v___y_2989_);
v_a_3003_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2990_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2990_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2976_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3020_, uint8_t v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
switch(lean_obj_tag(v_e_3020_))
{
case 7:
{
lean_object* v___x_3029_; 
v___x_3029_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3021_ == 0)
{
lean_object* v___x_3030_; lean_object* v_canon_3031_; lean_object* v_cache_3032_; lean_object* v___x_3033_; 
v___x_3030_ = lean_st_ref_get(v_a_3023_);
v_canon_3031_ = lean_ctor_get(v___x_3030_, 9);
lean_inc_ref(v_canon_3031_);
lean_dec(v___x_3030_);
v_cache_3032_ = lean_ctor_get(v_canon_3031_, 0);
lean_inc_ref(v_cache_3032_);
lean_dec_ref(v_canon_3031_);
v___x_3033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3032_, v_e_3020_);
lean_dec_ref(v_cache_3032_);
if (lean_obj_tag(v___x_3033_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_val_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set_tag(v___x_3036_, 0);
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_val_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
lean_object* v___x_3042_; 
lean_dec(v___x_3033_);
lean_inc_ref(v_e_3020_);
v___x_3042_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3029_, v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3081_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3081_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3081_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v_canon_3048_; lean_object* v_share_3049_; lean_object* v_maxFVar_3050_; lean_object* v_proofInstInfo_3051_; lean_object* v_inferType_3052_; lean_object* v_getLevel_3053_; lean_object* v_congrInfo_3054_; lean_object* v_defEqI_3055_; lean_object* v_extensions_3056_; lean_object* v_issues_3057_; lean_object* v_instanceOverrides_3058_; uint8_t v_debug_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3080_; 
v___x_3047_ = lean_st_ref_take(v_a_3023_);
v_canon_3048_ = lean_ctor_get(v___x_3047_, 9);
v_share_3049_ = lean_ctor_get(v___x_3047_, 0);
v_maxFVar_3050_ = lean_ctor_get(v___x_3047_, 1);
v_proofInstInfo_3051_ = lean_ctor_get(v___x_3047_, 2);
v_inferType_3052_ = lean_ctor_get(v___x_3047_, 3);
v_getLevel_3053_ = lean_ctor_get(v___x_3047_, 4);
v_congrInfo_3054_ = lean_ctor_get(v___x_3047_, 5);
v_defEqI_3055_ = lean_ctor_get(v___x_3047_, 6);
v_extensions_3056_ = lean_ctor_get(v___x_3047_, 7);
v_issues_3057_ = lean_ctor_get(v___x_3047_, 8);
v_instanceOverrides_3058_ = lean_ctor_get(v___x_3047_, 10);
v_debug_3059_ = lean_ctor_get_uint8(v___x_3047_, sizeof(void*)*11);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3061_ = v___x_3047_;
v_isShared_3062_ = v_isSharedCheck_3080_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_instanceOverrides_3058_);
lean_inc(v_canon_3048_);
lean_inc(v_issues_3057_);
lean_inc(v_extensions_3056_);
lean_inc(v_defEqI_3055_);
lean_inc(v_congrInfo_3054_);
lean_inc(v_getLevel_3053_);
lean_inc(v_inferType_3052_);
lean_inc(v_proofInstInfo_3051_);
lean_inc(v_maxFVar_3050_);
lean_inc(v_share_3049_);
lean_dec(v___x_3047_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3080_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_cache_3063_; lean_object* v_cacheInType_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3079_; 
v_cache_3063_ = lean_ctor_get(v_canon_3048_, 0);
v_cacheInType_3064_ = lean_ctor_get(v_canon_3048_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_canon_3048_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3066_ = v_canon_3048_;
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_cacheInType_3064_);
lean_inc(v_cache_3063_);
lean_dec(v_canon_3048_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_inc(v_a_3043_);
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3063_, v_e_3020_, v_a_3043_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_cacheInType_3064_);
v___x_3070_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 9, v___x_3070_);
v___x_3072_ = v___x_3061_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_share_3049_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_maxFVar_3050_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_proofInstInfo_3051_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_inferType_3052_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_getLevel_3053_);
lean_ctor_set(v_reuseFailAlloc_3077_, 5, v_congrInfo_3054_);
lean_ctor_set(v_reuseFailAlloc_3077_, 6, v_defEqI_3055_);
lean_ctor_set(v_reuseFailAlloc_3077_, 7, v_extensions_3056_);
lean_ctor_set(v_reuseFailAlloc_3077_, 8, v_issues_3057_);
lean_ctor_set(v_reuseFailAlloc_3077_, 9, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3077_, 10, v_instanceOverrides_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3077_, sizeof(void*)*11, v_debug_3059_);
v___x_3072_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_st_ref_put(v_a_3023_, v___x_3072_);
if (v_isShared_3046_ == 0)
{
v___x_3075_ = v___x_3045_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3043_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3042_;
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v_canon_3083_; lean_object* v_cacheInType_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_st_ref_get(v_a_3023_);
v_canon_3083_ = lean_ctor_get(v___x_3082_, 9);
lean_inc_ref(v_canon_3083_);
lean_dec(v___x_3082_);
v_cacheInType_3084_ = lean_ctor_get(v_canon_3083_, 1);
lean_inc_ref(v_cacheInType_3084_);
lean_dec_ref(v_canon_3083_);
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3084_, v_e_3020_);
lean_dec_ref(v_cacheInType_3084_);
if (lean_obj_tag(v___x_3085_) == 1)
{
lean_object* v_val_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_val_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set_tag(v___x_3088_, 0);
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_val_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v___x_3094_; 
lean_dec(v___x_3085_);
lean_inc_ref(v_e_3020_);
v___x_3094_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3029_, v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3133_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3133_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3133_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v_canon_3100_; lean_object* v_share_3101_; lean_object* v_maxFVar_3102_; lean_object* v_proofInstInfo_3103_; lean_object* v_inferType_3104_; lean_object* v_getLevel_3105_; lean_object* v_congrInfo_3106_; lean_object* v_defEqI_3107_; lean_object* v_extensions_3108_; lean_object* v_issues_3109_; lean_object* v_instanceOverrides_3110_; uint8_t v_debug_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3132_; 
v___x_3099_ = lean_st_ref_take(v_a_3023_);
v_canon_3100_ = lean_ctor_get(v___x_3099_, 9);
v_share_3101_ = lean_ctor_get(v___x_3099_, 0);
v_maxFVar_3102_ = lean_ctor_get(v___x_3099_, 1);
v_proofInstInfo_3103_ = lean_ctor_get(v___x_3099_, 2);
v_inferType_3104_ = lean_ctor_get(v___x_3099_, 3);
v_getLevel_3105_ = lean_ctor_get(v___x_3099_, 4);
v_congrInfo_3106_ = lean_ctor_get(v___x_3099_, 5);
v_defEqI_3107_ = lean_ctor_get(v___x_3099_, 6);
v_extensions_3108_ = lean_ctor_get(v___x_3099_, 7);
v_issues_3109_ = lean_ctor_get(v___x_3099_, 8);
v_instanceOverrides_3110_ = lean_ctor_get(v___x_3099_, 10);
v_debug_3111_ = lean_ctor_get_uint8(v___x_3099_, sizeof(void*)*11);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3113_ = v___x_3099_;
v_isShared_3114_ = v_isSharedCheck_3132_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_instanceOverrides_3110_);
lean_inc(v_canon_3100_);
lean_inc(v_issues_3109_);
lean_inc(v_extensions_3108_);
lean_inc(v_defEqI_3107_);
lean_inc(v_congrInfo_3106_);
lean_inc(v_getLevel_3105_);
lean_inc(v_inferType_3104_);
lean_inc(v_proofInstInfo_3103_);
lean_inc(v_maxFVar_3102_);
lean_inc(v_share_3101_);
lean_dec(v___x_3099_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3132_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_cache_3115_; lean_object* v_cacheInType_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3131_; 
v_cache_3115_ = lean_ctor_get(v_canon_3100_, 0);
v_cacheInType_3116_ = lean_ctor_get(v_canon_3100_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_canon_3100_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3118_ = v_canon_3100_;
v_isShared_3119_ = v_isSharedCheck_3131_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_cacheInType_3116_);
lean_inc(v_cache_3115_);
lean_dec(v_canon_3100_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3131_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_inc(v_a_3095_);
v___x_3120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3116_, v_e_3020_, v_a_3095_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v___x_3120_);
v___x_3122_ = v___x_3118_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_cache_3115_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 9, v___x_3122_);
v___x_3124_ = v___x_3113_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_share_3101_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_maxFVar_3102_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_proofInstInfo_3103_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v_inferType_3104_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v_getLevel_3105_);
lean_ctor_set(v_reuseFailAlloc_3129_, 5, v_congrInfo_3106_);
lean_ctor_set(v_reuseFailAlloc_3129_, 6, v_defEqI_3107_);
lean_ctor_set(v_reuseFailAlloc_3129_, 7, v_extensions_3108_);
lean_ctor_set(v_reuseFailAlloc_3129_, 8, v_issues_3109_);
lean_ctor_set(v_reuseFailAlloc_3129_, 9, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3129_, 10, v_instanceOverrides_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3129_, sizeof(void*)*11, v_debug_3111_);
v___x_3124_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_st_ref_put(v_a_3023_, v___x_3124_);
if (v_isShared_3098_ == 0)
{
v___x_3127_ = v___x_3097_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3095_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3094_;
}
}
}
}
case 6:
{
if (v_a_3021_ == 0)
{
lean_object* v___x_3134_; lean_object* v_canon_3135_; lean_object* v_cache_3136_; lean_object* v___x_3137_; 
v___x_3134_ = lean_st_ref_get(v_a_3023_);
v_canon_3135_ = lean_ctor_get(v___x_3134_, 9);
lean_inc_ref(v_canon_3135_);
lean_dec(v___x_3134_);
v_cache_3136_ = lean_ctor_get(v_canon_3135_, 0);
lean_inc_ref(v_cache_3136_);
lean_dec_ref(v_canon_3135_);
v___x_3137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3136_, v_e_3020_);
lean_dec_ref(v_cache_3136_);
if (lean_obj_tag(v___x_3137_) == 1)
{
lean_object* v_val_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_val_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set_tag(v___x_3140_, 0);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_val_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v___x_3146_; 
lean_dec(v___x_3137_);
lean_inc_ref(v_e_3020_);
v___x_3146_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3185_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3185_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3185_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v_canon_3152_; lean_object* v_share_3153_; lean_object* v_maxFVar_3154_; lean_object* v_proofInstInfo_3155_; lean_object* v_inferType_3156_; lean_object* v_getLevel_3157_; lean_object* v_congrInfo_3158_; lean_object* v_defEqI_3159_; lean_object* v_extensions_3160_; lean_object* v_issues_3161_; lean_object* v_instanceOverrides_3162_; uint8_t v_debug_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3184_; 
v___x_3151_ = lean_st_ref_take(v_a_3023_);
v_canon_3152_ = lean_ctor_get(v___x_3151_, 9);
v_share_3153_ = lean_ctor_get(v___x_3151_, 0);
v_maxFVar_3154_ = lean_ctor_get(v___x_3151_, 1);
v_proofInstInfo_3155_ = lean_ctor_get(v___x_3151_, 2);
v_inferType_3156_ = lean_ctor_get(v___x_3151_, 3);
v_getLevel_3157_ = lean_ctor_get(v___x_3151_, 4);
v_congrInfo_3158_ = lean_ctor_get(v___x_3151_, 5);
v_defEqI_3159_ = lean_ctor_get(v___x_3151_, 6);
v_extensions_3160_ = lean_ctor_get(v___x_3151_, 7);
v_issues_3161_ = lean_ctor_get(v___x_3151_, 8);
v_instanceOverrides_3162_ = lean_ctor_get(v___x_3151_, 10);
v_debug_3163_ = lean_ctor_get_uint8(v___x_3151_, sizeof(void*)*11);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3165_ = v___x_3151_;
v_isShared_3166_ = v_isSharedCheck_3184_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_instanceOverrides_3162_);
lean_inc(v_canon_3152_);
lean_inc(v_issues_3161_);
lean_inc(v_extensions_3160_);
lean_inc(v_defEqI_3159_);
lean_inc(v_congrInfo_3158_);
lean_inc(v_getLevel_3157_);
lean_inc(v_inferType_3156_);
lean_inc(v_proofInstInfo_3155_);
lean_inc(v_maxFVar_3154_);
lean_inc(v_share_3153_);
lean_dec(v___x_3151_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3184_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v_cache_3167_; lean_object* v_cacheInType_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3183_; 
v_cache_3167_ = lean_ctor_get(v_canon_3152_, 0);
v_cacheInType_3168_ = lean_ctor_get(v_canon_3152_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_canon_3152_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3170_ = v_canon_3152_;
v_isShared_3171_ = v_isSharedCheck_3183_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_cacheInType_3168_);
lean_inc(v_cache_3167_);
lean_dec(v_canon_3152_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3183_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
lean_inc(v_a_3147_);
v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3167_, v_e_3020_, v_a_3147_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_cacheInType_3168_);
v___x_3174_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3176_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 9, v___x_3174_);
v___x_3176_ = v___x_3165_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_share_3153_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_maxFVar_3154_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_proofInstInfo_3155_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_inferType_3156_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_getLevel_3157_);
lean_ctor_set(v_reuseFailAlloc_3181_, 5, v_congrInfo_3158_);
lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_defEqI_3159_);
lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_extensions_3160_);
lean_ctor_set(v_reuseFailAlloc_3181_, 8, v_issues_3161_);
lean_ctor_set(v_reuseFailAlloc_3181_, 9, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3181_, 10, v_instanceOverrides_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*11, v_debug_3163_);
v___x_3176_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = lean_st_ref_put(v_a_3023_, v___x_3176_);
if (v_isShared_3150_ == 0)
{
v___x_3179_ = v___x_3149_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3147_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3146_;
}
}
}
else
{
lean_object* v___x_3186_; lean_object* v_canon_3187_; lean_object* v_cacheInType_3188_; lean_object* v___x_3189_; 
v___x_3186_ = lean_st_ref_get(v_a_3023_);
v_canon_3187_ = lean_ctor_get(v___x_3186_, 9);
lean_inc_ref(v_canon_3187_);
lean_dec(v___x_3186_);
v_cacheInType_3188_ = lean_ctor_get(v_canon_3187_, 1);
lean_inc_ref(v_cacheInType_3188_);
lean_dec_ref(v_canon_3187_);
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3188_, v_e_3020_);
lean_dec_ref(v_cacheInType_3188_);
if (lean_obj_tag(v___x_3189_) == 1)
{
lean_object* v_val_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_val_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set_tag(v___x_3192_, 0);
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_val_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
else
{
lean_object* v___x_3198_; 
lean_dec(v___x_3189_);
lean_inc_ref(v_e_3020_);
v___x_3198_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3237_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3237_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3237_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v_canon_3204_; lean_object* v_share_3205_; lean_object* v_maxFVar_3206_; lean_object* v_proofInstInfo_3207_; lean_object* v_inferType_3208_; lean_object* v_getLevel_3209_; lean_object* v_congrInfo_3210_; lean_object* v_defEqI_3211_; lean_object* v_extensions_3212_; lean_object* v_issues_3213_; lean_object* v_instanceOverrides_3214_; uint8_t v_debug_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3236_; 
v___x_3203_ = lean_st_ref_take(v_a_3023_);
v_canon_3204_ = lean_ctor_get(v___x_3203_, 9);
v_share_3205_ = lean_ctor_get(v___x_3203_, 0);
v_maxFVar_3206_ = lean_ctor_get(v___x_3203_, 1);
v_proofInstInfo_3207_ = lean_ctor_get(v___x_3203_, 2);
v_inferType_3208_ = lean_ctor_get(v___x_3203_, 3);
v_getLevel_3209_ = lean_ctor_get(v___x_3203_, 4);
v_congrInfo_3210_ = lean_ctor_get(v___x_3203_, 5);
v_defEqI_3211_ = lean_ctor_get(v___x_3203_, 6);
v_extensions_3212_ = lean_ctor_get(v___x_3203_, 7);
v_issues_3213_ = lean_ctor_get(v___x_3203_, 8);
v_instanceOverrides_3214_ = lean_ctor_get(v___x_3203_, 10);
v_debug_3215_ = lean_ctor_get_uint8(v___x_3203_, sizeof(void*)*11);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3217_ = v___x_3203_;
v_isShared_3218_ = v_isSharedCheck_3236_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_instanceOverrides_3214_);
lean_inc(v_canon_3204_);
lean_inc(v_issues_3213_);
lean_inc(v_extensions_3212_);
lean_inc(v_defEqI_3211_);
lean_inc(v_congrInfo_3210_);
lean_inc(v_getLevel_3209_);
lean_inc(v_inferType_3208_);
lean_inc(v_proofInstInfo_3207_);
lean_inc(v_maxFVar_3206_);
lean_inc(v_share_3205_);
lean_dec(v___x_3203_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3236_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_cache_3219_; lean_object* v_cacheInType_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3235_; 
v_cache_3219_ = lean_ctor_get(v_canon_3204_, 0);
v_cacheInType_3220_ = lean_ctor_get(v_canon_3204_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_canon_3204_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3222_ = v_canon_3204_;
v_isShared_3223_ = v_isSharedCheck_3235_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_cacheInType_3220_);
lean_inc(v_cache_3219_);
lean_dec(v_canon_3204_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3235_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
lean_inc(v_a_3199_);
v___x_3224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3220_, v_e_3020_, v_a_3199_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v___x_3224_);
v___x_3226_ = v___x_3222_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_cache_3219_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 9, v___x_3226_);
v___x_3228_ = v___x_3217_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_share_3205_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_maxFVar_3206_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_proofInstInfo_3207_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_inferType_3208_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_getLevel_3209_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v_congrInfo_3210_);
lean_ctor_set(v_reuseFailAlloc_3233_, 6, v_defEqI_3211_);
lean_ctor_set(v_reuseFailAlloc_3233_, 7, v_extensions_3212_);
lean_ctor_set(v_reuseFailAlloc_3233_, 8, v_issues_3213_);
lean_ctor_set(v_reuseFailAlloc_3233_, 9, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3233_, 10, v_instanceOverrides_3214_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*11, v_debug_3215_);
v___x_3228_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_st_ref_put(v_a_3023_, v___x_3228_);
if (v_isShared_3202_ == 0)
{
v___x_3231_ = v___x_3201_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3199_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3198_;
}
}
}
}
case 8:
{
lean_object* v___x_3238_; 
v___x_3238_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3021_ == 0)
{
lean_object* v___x_3239_; lean_object* v_canon_3240_; lean_object* v_cache_3241_; lean_object* v___x_3242_; 
v___x_3239_ = lean_st_ref_get(v_a_3023_);
v_canon_3240_ = lean_ctor_get(v___x_3239_, 9);
lean_inc_ref(v_canon_3240_);
lean_dec(v___x_3239_);
v_cache_3241_ = lean_ctor_get(v_canon_3240_, 0);
lean_inc_ref(v_cache_3241_);
lean_dec_ref(v_canon_3240_);
v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3241_, v_e_3020_);
lean_dec_ref(v_cache_3241_);
if (lean_obj_tag(v___x_3242_) == 1)
{
lean_object* v_val_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref_known(v_e_3020_, 4);
v_val_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_val_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set_tag(v___x_3245_, 0);
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_val_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
else
{
lean_object* v___x_3251_; 
lean_dec(v___x_3242_);
lean_inc_ref(v_e_3020_);
v___x_3251_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3238_, v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3290_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3290_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3290_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v_canon_3257_; lean_object* v_share_3258_; lean_object* v_maxFVar_3259_; lean_object* v_proofInstInfo_3260_; lean_object* v_inferType_3261_; lean_object* v_getLevel_3262_; lean_object* v_congrInfo_3263_; lean_object* v_defEqI_3264_; lean_object* v_extensions_3265_; lean_object* v_issues_3266_; lean_object* v_instanceOverrides_3267_; uint8_t v_debug_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3289_; 
v___x_3256_ = lean_st_ref_take(v_a_3023_);
v_canon_3257_ = lean_ctor_get(v___x_3256_, 9);
v_share_3258_ = lean_ctor_get(v___x_3256_, 0);
v_maxFVar_3259_ = lean_ctor_get(v___x_3256_, 1);
v_proofInstInfo_3260_ = lean_ctor_get(v___x_3256_, 2);
v_inferType_3261_ = lean_ctor_get(v___x_3256_, 3);
v_getLevel_3262_ = lean_ctor_get(v___x_3256_, 4);
v_congrInfo_3263_ = lean_ctor_get(v___x_3256_, 5);
v_defEqI_3264_ = lean_ctor_get(v___x_3256_, 6);
v_extensions_3265_ = lean_ctor_get(v___x_3256_, 7);
v_issues_3266_ = lean_ctor_get(v___x_3256_, 8);
v_instanceOverrides_3267_ = lean_ctor_get(v___x_3256_, 10);
v_debug_3268_ = lean_ctor_get_uint8(v___x_3256_, sizeof(void*)*11);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3270_ = v___x_3256_;
v_isShared_3271_ = v_isSharedCheck_3289_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_instanceOverrides_3267_);
lean_inc(v_canon_3257_);
lean_inc(v_issues_3266_);
lean_inc(v_extensions_3265_);
lean_inc(v_defEqI_3264_);
lean_inc(v_congrInfo_3263_);
lean_inc(v_getLevel_3262_);
lean_inc(v_inferType_3261_);
lean_inc(v_proofInstInfo_3260_);
lean_inc(v_maxFVar_3259_);
lean_inc(v_share_3258_);
lean_dec(v___x_3256_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3289_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v_cache_3272_; lean_object* v_cacheInType_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3288_; 
v_cache_3272_ = lean_ctor_get(v_canon_3257_, 0);
v_cacheInType_3273_ = lean_ctor_get(v_canon_3257_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_canon_3257_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3275_ = v_canon_3257_;
v_isShared_3276_ = v_isSharedCheck_3288_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_cacheInType_3273_);
lean_inc(v_cache_3272_);
lean_dec(v_canon_3257_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3288_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_inc(v_a_3252_);
v___x_3277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3272_, v_e_3020_, v_a_3252_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3277_);
v___x_3279_ = v___x_3275_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_cacheInType_3273_);
v___x_3279_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3281_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 9, v___x_3279_);
v___x_3281_ = v___x_3270_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_share_3258_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_maxFVar_3259_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_proofInstInfo_3260_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_inferType_3261_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_getLevel_3262_);
lean_ctor_set(v_reuseFailAlloc_3286_, 5, v_congrInfo_3263_);
lean_ctor_set(v_reuseFailAlloc_3286_, 6, v_defEqI_3264_);
lean_ctor_set(v_reuseFailAlloc_3286_, 7, v_extensions_3265_);
lean_ctor_set(v_reuseFailAlloc_3286_, 8, v_issues_3266_);
lean_ctor_set(v_reuseFailAlloc_3286_, 9, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 10, v_instanceOverrides_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3286_, sizeof(void*)*11, v_debug_3268_);
v___x_3281_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = lean_st_ref_put(v_a_3023_, v___x_3281_);
if (v_isShared_3255_ == 0)
{
v___x_3284_ = v___x_3254_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3252_);
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
}
}
else
{
lean_dec_ref_known(v_e_3020_, 4);
return v___x_3251_;
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v_canon_3292_; lean_object* v_cacheInType_3293_; lean_object* v___x_3294_; 
v___x_3291_ = lean_st_ref_get(v_a_3023_);
v_canon_3292_ = lean_ctor_get(v___x_3291_, 9);
lean_inc_ref(v_canon_3292_);
lean_dec(v___x_3291_);
v_cacheInType_3293_ = lean_ctor_get(v_canon_3292_, 1);
lean_inc_ref(v_cacheInType_3293_);
lean_dec_ref(v_canon_3292_);
v___x_3294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3293_, v_e_3020_);
lean_dec_ref(v_cacheInType_3293_);
if (lean_obj_tag(v___x_3294_) == 1)
{
lean_object* v_val_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref_known(v_e_3020_, 4);
v_val_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_val_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 0);
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v___x_3303_; 
lean_dec(v___x_3294_);
lean_inc_ref(v_e_3020_);
v___x_3303_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3238_, v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3342_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3342_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3342_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v_canon_3309_; lean_object* v_share_3310_; lean_object* v_maxFVar_3311_; lean_object* v_proofInstInfo_3312_; lean_object* v_inferType_3313_; lean_object* v_getLevel_3314_; lean_object* v_congrInfo_3315_; lean_object* v_defEqI_3316_; lean_object* v_extensions_3317_; lean_object* v_issues_3318_; lean_object* v_instanceOverrides_3319_; uint8_t v_debug_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3341_; 
v___x_3308_ = lean_st_ref_take(v_a_3023_);
v_canon_3309_ = lean_ctor_get(v___x_3308_, 9);
v_share_3310_ = lean_ctor_get(v___x_3308_, 0);
v_maxFVar_3311_ = lean_ctor_get(v___x_3308_, 1);
v_proofInstInfo_3312_ = lean_ctor_get(v___x_3308_, 2);
v_inferType_3313_ = lean_ctor_get(v___x_3308_, 3);
v_getLevel_3314_ = lean_ctor_get(v___x_3308_, 4);
v_congrInfo_3315_ = lean_ctor_get(v___x_3308_, 5);
v_defEqI_3316_ = lean_ctor_get(v___x_3308_, 6);
v_extensions_3317_ = lean_ctor_get(v___x_3308_, 7);
v_issues_3318_ = lean_ctor_get(v___x_3308_, 8);
v_instanceOverrides_3319_ = lean_ctor_get(v___x_3308_, 10);
v_debug_3320_ = lean_ctor_get_uint8(v___x_3308_, sizeof(void*)*11);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3322_ = v___x_3308_;
v_isShared_3323_ = v_isSharedCheck_3341_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_instanceOverrides_3319_);
lean_inc(v_canon_3309_);
lean_inc(v_issues_3318_);
lean_inc(v_extensions_3317_);
lean_inc(v_defEqI_3316_);
lean_inc(v_congrInfo_3315_);
lean_inc(v_getLevel_3314_);
lean_inc(v_inferType_3313_);
lean_inc(v_proofInstInfo_3312_);
lean_inc(v_maxFVar_3311_);
lean_inc(v_share_3310_);
lean_dec(v___x_3308_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3341_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_cache_3324_; lean_object* v_cacheInType_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3340_; 
v_cache_3324_ = lean_ctor_get(v_canon_3309_, 0);
v_cacheInType_3325_ = lean_ctor_get(v_canon_3309_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_canon_3309_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3327_ = v_canon_3309_;
v_isShared_3328_ = v_isSharedCheck_3340_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_cacheInType_3325_);
lean_inc(v_cache_3324_);
lean_dec(v_canon_3309_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3340_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
lean_inc(v_a_3304_);
v___x_3329_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3325_, v_e_3020_, v_a_3304_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3329_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_cache_3324_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3333_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 9, v___x_3331_);
v___x_3333_ = v___x_3322_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_share_3310_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_maxFVar_3311_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_proofInstInfo_3312_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_inferType_3313_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v_getLevel_3314_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v_congrInfo_3315_);
lean_ctor_set(v_reuseFailAlloc_3338_, 6, v_defEqI_3316_);
lean_ctor_set(v_reuseFailAlloc_3338_, 7, v_extensions_3317_);
lean_ctor_set(v_reuseFailAlloc_3338_, 8, v_issues_3318_);
lean_ctor_set(v_reuseFailAlloc_3338_, 9, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3338_, 10, v_instanceOverrides_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3338_, sizeof(void*)*11, v_debug_3320_);
v___x_3333_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_st_ref_put(v_a_3023_, v___x_3333_);
if (v_isShared_3307_ == 0)
{
v___x_3336_ = v___x_3306_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3304_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 4);
return v___x_3303_;
}
}
}
}
case 5:
{
if (v_a_3021_ == 0)
{
lean_object* v___x_3343_; lean_object* v_canon_3344_; lean_object* v_cache_3345_; lean_object* v___x_3346_; 
v___x_3343_ = lean_st_ref_get(v_a_3023_);
v_canon_3344_ = lean_ctor_get(v___x_3343_, 9);
lean_inc_ref(v_canon_3344_);
lean_dec(v___x_3343_);
v_cache_3345_ = lean_ctor_get(v_canon_3344_, 0);
lean_inc_ref(v_cache_3345_);
lean_dec_ref(v_canon_3344_);
v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3345_, v_e_3020_);
lean_dec_ref(v_cache_3345_);
if (lean_obj_tag(v___x_3346_) == 1)
{
lean_object* v_val_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref_known(v_e_3020_, 2);
v_val_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_val_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 0);
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_val_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
else
{
lean_object* v___x_3355_; 
lean_dec(v___x_3346_);
lean_inc_ref(v_e_3020_);
v___x_3355_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3394_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3394_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3394_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v_canon_3361_; lean_object* v_share_3362_; lean_object* v_maxFVar_3363_; lean_object* v_proofInstInfo_3364_; lean_object* v_inferType_3365_; lean_object* v_getLevel_3366_; lean_object* v_congrInfo_3367_; lean_object* v_defEqI_3368_; lean_object* v_extensions_3369_; lean_object* v_issues_3370_; lean_object* v_instanceOverrides_3371_; uint8_t v_debug_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3393_; 
v___x_3360_ = lean_st_ref_take(v_a_3023_);
v_canon_3361_ = lean_ctor_get(v___x_3360_, 9);
v_share_3362_ = lean_ctor_get(v___x_3360_, 0);
v_maxFVar_3363_ = lean_ctor_get(v___x_3360_, 1);
v_proofInstInfo_3364_ = lean_ctor_get(v___x_3360_, 2);
v_inferType_3365_ = lean_ctor_get(v___x_3360_, 3);
v_getLevel_3366_ = lean_ctor_get(v___x_3360_, 4);
v_congrInfo_3367_ = lean_ctor_get(v___x_3360_, 5);
v_defEqI_3368_ = lean_ctor_get(v___x_3360_, 6);
v_extensions_3369_ = lean_ctor_get(v___x_3360_, 7);
v_issues_3370_ = lean_ctor_get(v___x_3360_, 8);
v_instanceOverrides_3371_ = lean_ctor_get(v___x_3360_, 10);
v_debug_3372_ = lean_ctor_get_uint8(v___x_3360_, sizeof(void*)*11);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3374_ = v___x_3360_;
v_isShared_3375_ = v_isSharedCheck_3393_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_instanceOverrides_3371_);
lean_inc(v_canon_3361_);
lean_inc(v_issues_3370_);
lean_inc(v_extensions_3369_);
lean_inc(v_defEqI_3368_);
lean_inc(v_congrInfo_3367_);
lean_inc(v_getLevel_3366_);
lean_inc(v_inferType_3365_);
lean_inc(v_proofInstInfo_3364_);
lean_inc(v_maxFVar_3363_);
lean_inc(v_share_3362_);
lean_dec(v___x_3360_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3393_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_cache_3376_; lean_object* v_cacheInType_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3392_; 
v_cache_3376_ = lean_ctor_get(v_canon_3361_, 0);
v_cacheInType_3377_ = lean_ctor_get(v_canon_3361_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_canon_3361_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3379_ = v_canon_3361_;
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_cacheInType_3377_);
lean_inc(v_cache_3376_);
lean_dec(v_canon_3361_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_inc(v_a_3356_);
v___x_3381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3376_, v_e_3020_, v_a_3356_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_cacheInType_3377_);
v___x_3383_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 9, v___x_3383_);
v___x_3385_ = v___x_3374_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_share_3362_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_maxFVar_3363_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_proofInstInfo_3364_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_inferType_3365_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_getLevel_3366_);
lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_congrInfo_3367_);
lean_ctor_set(v_reuseFailAlloc_3390_, 6, v_defEqI_3368_);
lean_ctor_set(v_reuseFailAlloc_3390_, 7, v_extensions_3369_);
lean_ctor_set(v_reuseFailAlloc_3390_, 8, v_issues_3370_);
lean_ctor_set(v_reuseFailAlloc_3390_, 9, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3390_, 10, v_instanceOverrides_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3390_, sizeof(void*)*11, v_debug_3372_);
v___x_3385_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_st_ref_put(v_a_3023_, v___x_3385_);
if (v_isShared_3359_ == 0)
{
v___x_3388_ = v___x_3358_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3356_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 2);
return v___x_3355_;
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v_canon_3396_; lean_object* v_cacheInType_3397_; lean_object* v___x_3398_; 
v___x_3395_ = lean_st_ref_get(v_a_3023_);
v_canon_3396_ = lean_ctor_get(v___x_3395_, 9);
lean_inc_ref(v_canon_3396_);
lean_dec(v___x_3395_);
v_cacheInType_3397_ = lean_ctor_get(v_canon_3396_, 1);
lean_inc_ref(v_cacheInType_3397_);
lean_dec_ref(v_canon_3396_);
v___x_3398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3397_, v_e_3020_);
lean_dec_ref(v_cacheInType_3397_);
if (lean_obj_tag(v___x_3398_) == 1)
{
lean_object* v_val_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref_known(v_e_3020_, 2);
v_val_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_val_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 0);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_val_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
else
{
lean_object* v___x_3407_; 
lean_dec(v___x_3398_);
lean_inc_ref(v_e_3020_);
v___x_3407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3446_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3446_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3446_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v_canon_3413_; lean_object* v_share_3414_; lean_object* v_maxFVar_3415_; lean_object* v_proofInstInfo_3416_; lean_object* v_inferType_3417_; lean_object* v_getLevel_3418_; lean_object* v_congrInfo_3419_; lean_object* v_defEqI_3420_; lean_object* v_extensions_3421_; lean_object* v_issues_3422_; lean_object* v_instanceOverrides_3423_; uint8_t v_debug_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3445_; 
v___x_3412_ = lean_st_ref_take(v_a_3023_);
v_canon_3413_ = lean_ctor_get(v___x_3412_, 9);
v_share_3414_ = lean_ctor_get(v___x_3412_, 0);
v_maxFVar_3415_ = lean_ctor_get(v___x_3412_, 1);
v_proofInstInfo_3416_ = lean_ctor_get(v___x_3412_, 2);
v_inferType_3417_ = lean_ctor_get(v___x_3412_, 3);
v_getLevel_3418_ = lean_ctor_get(v___x_3412_, 4);
v_congrInfo_3419_ = lean_ctor_get(v___x_3412_, 5);
v_defEqI_3420_ = lean_ctor_get(v___x_3412_, 6);
v_extensions_3421_ = lean_ctor_get(v___x_3412_, 7);
v_issues_3422_ = lean_ctor_get(v___x_3412_, 8);
v_instanceOverrides_3423_ = lean_ctor_get(v___x_3412_, 10);
v_debug_3424_ = lean_ctor_get_uint8(v___x_3412_, sizeof(void*)*11);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3426_ = v___x_3412_;
v_isShared_3427_ = v_isSharedCheck_3445_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_instanceOverrides_3423_);
lean_inc(v_canon_3413_);
lean_inc(v_issues_3422_);
lean_inc(v_extensions_3421_);
lean_inc(v_defEqI_3420_);
lean_inc(v_congrInfo_3419_);
lean_inc(v_getLevel_3418_);
lean_inc(v_inferType_3417_);
lean_inc(v_proofInstInfo_3416_);
lean_inc(v_maxFVar_3415_);
lean_inc(v_share_3414_);
lean_dec(v___x_3412_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3445_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_cache_3428_; lean_object* v_cacheInType_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3444_; 
v_cache_3428_ = lean_ctor_get(v_canon_3413_, 0);
v_cacheInType_3429_ = lean_ctor_get(v_canon_3413_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_canon_3413_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3431_ = v_canon_3413_;
v_isShared_3432_ = v_isSharedCheck_3444_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_cacheInType_3429_);
lean_inc(v_cache_3428_);
lean_dec(v_canon_3413_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3444_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_inc(v_a_3408_);
v___x_3433_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3429_, v_e_3020_, v_a_3408_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3433_);
v___x_3435_ = v___x_3431_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_cache_3428_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3437_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 9, v___x_3435_);
v___x_3437_ = v___x_3426_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_share_3414_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_maxFVar_3415_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_proofInstInfo_3416_);
lean_ctor_set(v_reuseFailAlloc_3442_, 3, v_inferType_3417_);
lean_ctor_set(v_reuseFailAlloc_3442_, 4, v_getLevel_3418_);
lean_ctor_set(v_reuseFailAlloc_3442_, 5, v_congrInfo_3419_);
lean_ctor_set(v_reuseFailAlloc_3442_, 6, v_defEqI_3420_);
lean_ctor_set(v_reuseFailAlloc_3442_, 7, v_extensions_3421_);
lean_ctor_set(v_reuseFailAlloc_3442_, 8, v_issues_3422_);
lean_ctor_set(v_reuseFailAlloc_3442_, 9, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3442_, 10, v_instanceOverrides_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3442_, sizeof(void*)*11, v_debug_3424_);
v___x_3437_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_st_ref_put(v_a_3023_, v___x_3437_);
if (v_isShared_3411_ == 0)
{
v___x_3440_ = v___x_3410_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3408_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 2);
return v___x_3407_;
}
}
}
}
case 11:
{
if (v_a_3021_ == 0)
{
lean_object* v___x_3447_; lean_object* v_canon_3448_; lean_object* v_cache_3449_; lean_object* v___x_3450_; 
v___x_3447_ = lean_st_ref_get(v_a_3023_);
v_canon_3448_ = lean_ctor_get(v___x_3447_, 9);
lean_inc_ref(v_canon_3448_);
lean_dec(v___x_3447_);
v_cache_3449_ = lean_ctor_get(v_canon_3448_, 0);
lean_inc_ref(v_cache_3449_);
lean_dec_ref(v_canon_3448_);
v___x_3450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3449_, v_e_3020_);
lean_dec_ref(v_cache_3449_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_val_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_val_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set_tag(v___x_3453_, 0);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_val_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_object* v___x_3459_; 
lean_dec(v___x_3450_);
lean_inc_ref(v_e_3020_);
v___x_3459_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3498_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3498_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3498_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v_canon_3465_; lean_object* v_share_3466_; lean_object* v_maxFVar_3467_; lean_object* v_proofInstInfo_3468_; lean_object* v_inferType_3469_; lean_object* v_getLevel_3470_; lean_object* v_congrInfo_3471_; lean_object* v_defEqI_3472_; lean_object* v_extensions_3473_; lean_object* v_issues_3474_; lean_object* v_instanceOverrides_3475_; uint8_t v_debug_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3497_; 
v___x_3464_ = lean_st_ref_take(v_a_3023_);
v_canon_3465_ = lean_ctor_get(v___x_3464_, 9);
v_share_3466_ = lean_ctor_get(v___x_3464_, 0);
v_maxFVar_3467_ = lean_ctor_get(v___x_3464_, 1);
v_proofInstInfo_3468_ = lean_ctor_get(v___x_3464_, 2);
v_inferType_3469_ = lean_ctor_get(v___x_3464_, 3);
v_getLevel_3470_ = lean_ctor_get(v___x_3464_, 4);
v_congrInfo_3471_ = lean_ctor_get(v___x_3464_, 5);
v_defEqI_3472_ = lean_ctor_get(v___x_3464_, 6);
v_extensions_3473_ = lean_ctor_get(v___x_3464_, 7);
v_issues_3474_ = lean_ctor_get(v___x_3464_, 8);
v_instanceOverrides_3475_ = lean_ctor_get(v___x_3464_, 10);
v_debug_3476_ = lean_ctor_get_uint8(v___x_3464_, sizeof(void*)*11);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3478_ = v___x_3464_;
v_isShared_3479_ = v_isSharedCheck_3497_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_instanceOverrides_3475_);
lean_inc(v_canon_3465_);
lean_inc(v_issues_3474_);
lean_inc(v_extensions_3473_);
lean_inc(v_defEqI_3472_);
lean_inc(v_congrInfo_3471_);
lean_inc(v_getLevel_3470_);
lean_inc(v_inferType_3469_);
lean_inc(v_proofInstInfo_3468_);
lean_inc(v_maxFVar_3467_);
lean_inc(v_share_3466_);
lean_dec(v___x_3464_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3497_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_cache_3480_; lean_object* v_cacheInType_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3496_; 
v_cache_3480_ = lean_ctor_get(v_canon_3465_, 0);
v_cacheInType_3481_ = lean_ctor_get(v_canon_3465_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_canon_3465_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3483_ = v_canon_3465_;
v_isShared_3484_ = v_isSharedCheck_3496_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_cacheInType_3481_);
lean_inc(v_cache_3480_);
lean_dec(v_canon_3465_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3496_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
lean_inc(v_a_3460_);
v___x_3485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3480_, v_e_3020_, v_a_3460_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3485_);
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_cacheInType_3481_);
v___x_3487_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3489_; 
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 9, v___x_3487_);
v___x_3489_ = v___x_3478_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_share_3466_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_maxFVar_3467_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_proofInstInfo_3468_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_inferType_3469_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_getLevel_3470_);
lean_ctor_set(v_reuseFailAlloc_3494_, 5, v_congrInfo_3471_);
lean_ctor_set(v_reuseFailAlloc_3494_, 6, v_defEqI_3472_);
lean_ctor_set(v_reuseFailAlloc_3494_, 7, v_extensions_3473_);
lean_ctor_set(v_reuseFailAlloc_3494_, 8, v_issues_3474_);
lean_ctor_set(v_reuseFailAlloc_3494_, 9, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3494_, 10, v_instanceOverrides_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3494_, sizeof(void*)*11, v_debug_3476_);
v___x_3489_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = lean_st_ref_put(v_a_3023_, v___x_3489_);
if (v_isShared_3463_ == 0)
{
v___x_3492_ = v___x_3462_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3460_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3459_;
}
}
}
else
{
lean_object* v___x_3499_; lean_object* v_canon_3500_; lean_object* v_cacheInType_3501_; lean_object* v___x_3502_; 
v___x_3499_ = lean_st_ref_get(v_a_3023_);
v_canon_3500_ = lean_ctor_get(v___x_3499_, 9);
lean_inc_ref(v_canon_3500_);
lean_dec(v___x_3499_);
v_cacheInType_3501_ = lean_ctor_get(v_canon_3500_, 1);
lean_inc_ref(v_cacheInType_3501_);
lean_dec_ref(v_canon_3500_);
v___x_3502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3501_, v_e_3020_);
lean_dec_ref(v_cacheInType_3501_);
if (lean_obj_tag(v___x_3502_) == 1)
{
lean_object* v_val_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref_known(v_e_3020_, 3);
v_val_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_val_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set_tag(v___x_3505_, 0);
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_val_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3502_);
lean_inc_ref(v_e_3020_);
v___x_3511_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3550_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3550_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3550_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v_canon_3517_; lean_object* v_share_3518_; lean_object* v_maxFVar_3519_; lean_object* v_proofInstInfo_3520_; lean_object* v_inferType_3521_; lean_object* v_getLevel_3522_; lean_object* v_congrInfo_3523_; lean_object* v_defEqI_3524_; lean_object* v_extensions_3525_; lean_object* v_issues_3526_; lean_object* v_instanceOverrides_3527_; uint8_t v_debug_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3549_; 
v___x_3516_ = lean_st_ref_take(v_a_3023_);
v_canon_3517_ = lean_ctor_get(v___x_3516_, 9);
v_share_3518_ = lean_ctor_get(v___x_3516_, 0);
v_maxFVar_3519_ = lean_ctor_get(v___x_3516_, 1);
v_proofInstInfo_3520_ = lean_ctor_get(v___x_3516_, 2);
v_inferType_3521_ = lean_ctor_get(v___x_3516_, 3);
v_getLevel_3522_ = lean_ctor_get(v___x_3516_, 4);
v_congrInfo_3523_ = lean_ctor_get(v___x_3516_, 5);
v_defEqI_3524_ = lean_ctor_get(v___x_3516_, 6);
v_extensions_3525_ = lean_ctor_get(v___x_3516_, 7);
v_issues_3526_ = lean_ctor_get(v___x_3516_, 8);
v_instanceOverrides_3527_ = lean_ctor_get(v___x_3516_, 10);
v_debug_3528_ = lean_ctor_get_uint8(v___x_3516_, sizeof(void*)*11);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3530_ = v___x_3516_;
v_isShared_3531_ = v_isSharedCheck_3549_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_instanceOverrides_3527_);
lean_inc(v_canon_3517_);
lean_inc(v_issues_3526_);
lean_inc(v_extensions_3525_);
lean_inc(v_defEqI_3524_);
lean_inc(v_congrInfo_3523_);
lean_inc(v_getLevel_3522_);
lean_inc(v_inferType_3521_);
lean_inc(v_proofInstInfo_3520_);
lean_inc(v_maxFVar_3519_);
lean_inc(v_share_3518_);
lean_dec(v___x_3516_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3549_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_cache_3532_; lean_object* v_cacheInType_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3548_; 
v_cache_3532_ = lean_ctor_get(v_canon_3517_, 0);
v_cacheInType_3533_ = lean_ctor_get(v_canon_3517_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_canon_3517_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3535_ = v_canon_3517_;
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_cacheInType_3533_);
lean_inc(v_cache_3532_);
lean_dec(v_canon_3517_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
lean_inc(v_a_3512_);
v___x_3537_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3533_, v_e_3020_, v_a_3512_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v___x_3537_);
v___x_3539_ = v___x_3535_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_cache_3532_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 9, v___x_3539_);
v___x_3541_ = v___x_3530_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_share_3518_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_maxFVar_3519_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_proofInstInfo_3520_);
lean_ctor_set(v_reuseFailAlloc_3546_, 3, v_inferType_3521_);
lean_ctor_set(v_reuseFailAlloc_3546_, 4, v_getLevel_3522_);
lean_ctor_set(v_reuseFailAlloc_3546_, 5, v_congrInfo_3523_);
lean_ctor_set(v_reuseFailAlloc_3546_, 6, v_defEqI_3524_);
lean_ctor_set(v_reuseFailAlloc_3546_, 7, v_extensions_3525_);
lean_ctor_set(v_reuseFailAlloc_3546_, 8, v_issues_3526_);
lean_ctor_set(v_reuseFailAlloc_3546_, 9, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3546_, 10, v_instanceOverrides_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3546_, sizeof(void*)*11, v_debug_3528_);
v___x_3541_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = lean_st_ref_put(v_a_3023_, v___x_3541_);
if (v_isShared_3515_ == 0)
{
v___x_3544_ = v___x_3514_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3512_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 3);
return v___x_3511_;
}
}
}
}
case 10:
{
lean_object* v_data_3551_; lean_object* v_expr_3552_; lean_object* v___x_3553_; 
v_data_3551_ = lean_ctor_get(v_e_3020_, 0);
v_expr_3552_ = lean_ctor_get(v_e_3020_, 1);
lean_inc_ref(v_expr_3552_);
v___x_3553_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3552_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3568_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3568_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3568_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
size_t v___x_3558_; size_t v___x_3559_; uint8_t v___x_3560_; 
v___x_3558_ = lean_ptr_addr(v_expr_3552_);
v___x_3559_ = lean_ptr_addr(v_a_3554_);
v___x_3560_ = lean_usize_dec_eq(v___x_3558_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_inc(v_data_3551_);
lean_dec_ref_known(v_e_3020_, 2);
v___x_3561_ = l_Lean_Expr_mdata___override(v_data_3551_, v_a_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3561_);
v___x_3563_ = v___x_3556_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
else
{
lean_object* v___x_3566_; 
lean_dec(v_a_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v_e_3020_);
v___x_3566_ = v___x_3556_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_e_3020_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3020_, 2);
return v___x_3553_;
}
}
default: 
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_e_3020_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3570_, uint8_t v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
if (v_a_3571_ == 0)
{
lean_object* v___x_3579_; 
lean_inc_ref(v_e_3570_);
v___x_3579_ = l_Lean_Meta_isProp(v_e_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; uint8_t v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3581_ = lean_unbox(v_a_3580_);
lean_dec(v_a_3580_);
if (v___x_3581_ == 0)
{
uint8_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = 1;
v___x_3583_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3570_, v___x_3582_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3583_;
}
else
{
lean_object* v___x_3584_; 
v___x_3584_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3584_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v_e_3570_);
v_a_3585_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3579_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3579_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3594_, lean_object* v_body_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
uint8_t v___y_61750__boxed_3605_; lean_object* v_res_3606_; 
v___y_61750__boxed_3605_ = lean_unbox(v___y_3597_);
v_res_3606_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3594_, v_body_3595_, v_x_3596_, v___y_61750__boxed_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3607_, lean_object* v_e_3608_, uint8_t v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
if (lean_obj_tag(v_e_3608_) == 7)
{
lean_object* v_binderName_3617_; lean_object* v_binderType_3618_; lean_object* v_body_3619_; uint8_t v_binderInfo_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_binderName_3617_ = lean_ctor_get(v_e_3608_, 0);
lean_inc(v_binderName_3617_);
v_binderType_3618_ = lean_ctor_get(v_e_3608_, 1);
lean_inc_ref(v_binderType_3618_);
v_body_3619_ = lean_ctor_get(v_e_3608_, 2);
lean_inc_ref(v_body_3619_);
v_binderInfo_3620_ = lean_ctor_get_uint8(v_e_3608_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3608_, 3);
v___x_3621_ = lean_expr_instantiate_rev(v_binderType_3618_, v_fvars_3607_);
lean_dec_ref(v_binderType_3618_);
v___x_3622_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3621_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___f_3624_; uint8_t v___x_3625_; lean_object* v___x_3626_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v___f_3624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3624_, 0, v_fvars_3607_);
lean_closure_set(v___f_3624_, 1, v_body_3619_);
v___x_3625_ = 0;
v___x_3626_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_3617_, v_binderInfo_3620_, v_a_3623_, v___f_3624_, v___x_3625_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
return v___x_3626_;
}
else
{
lean_dec_ref(v_body_3619_);
lean_dec(v_binderName_3617_);
lean_dec_ref(v_fvars_3607_);
return v___x_3622_;
}
}
else
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = lean_expr_instantiate_rev(v_e_3608_, v_fvars_3607_);
lean_dec_ref(v_e_3608_);
v___x_3628_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3627_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; uint8_t v___x_3630_; uint8_t v___x_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3630_ = 0;
v___x_3631_ = 1;
v___x_3632_ = 1;
v___x_3633_ = l_Lean_Meta_mkForallFVars(v_fvars_3607_, v_a_3629_, v___x_3630_, v___x_3631_, v___x_3631_, v___x_3632_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
lean_dec_ref(v_fvars_3607_);
return v___x_3633_;
}
else
{
lean_dec_ref(v_fvars_3607_);
return v___x_3628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3634_, lean_object* v_body_3635_, lean_object* v_x_3636_, uint8_t v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_array_push(v_fvars_3634_, v_x_3636_);
v___x_3646_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3645_, v_body_3635_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
uint8_t v_a_boxed_3656_; lean_object* v_res_3657_; 
v_a_boxed_3656_ = lean_unbox(v_a_3648_);
v_res_3657_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3647_, v_a_boxed_3656_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v_a_boxed_3667_; lean_object* v_res_3668_; 
v_a_boxed_3667_ = lean_unbox(v_a_3659_);
v_res_3668_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3658_, v_a_boxed_3667_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
uint8_t v_a_boxed_3678_; lean_object* v_res_3679_; 
v_a_boxed_3678_ = lean_unbox(v_a_3670_);
v_res_3679_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3669_, v_a_boxed_3678_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
uint8_t v_a_boxed_3689_; lean_object* v_res_3690_; 
v_a_boxed_3689_ = lean_unbox(v_a_3681_);
v_res_3690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3680_, v_a_boxed_3689_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
uint8_t v_a_boxed_3700_; lean_object* v_res_3701_; 
v_a_boxed_3700_ = lean_unbox(v_a_3692_);
v_res_3701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3691_, v_a_boxed_3700_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3702_, lean_object* v_e_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
uint8_t v_a_boxed_3712_; lean_object* v_res_3713_; 
v_a_boxed_3712_ = lean_unbox(v_a_3704_);
v_res_3713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3702_, v_e_3703_, v_a_boxed_3712_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3714_, lean_object* v_e_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
uint8_t v_a_boxed_3724_; lean_object* v_res_3725_; 
v_a_boxed_3724_ = lean_unbox(v_a_3716_);
v_res_3725_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3714_, v_e_3715_, v_a_boxed_3724_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3726_, lean_object* v_report_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
uint8_t v_report_boxed_3736_; uint8_t v_a_boxed_3737_; lean_object* v_res_3738_; 
v_report_boxed_3736_ = lean_unbox(v_report_3727_);
v_a_boxed_3737_ = lean_unbox(v_a_3728_);
v_res_3738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3726_, v_report_boxed_3736_, v_a_boxed_3737_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
uint8_t v_a_boxed_3748_; lean_object* v_res_3749_; 
v_a_boxed_3748_ = lean_unbox(v_a_3740_);
v_res_3749_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3739_, v_a_boxed_3748_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3750_, lean_object* v_e_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_){
_start:
{
uint8_t v_a_boxed_3760_; lean_object* v_res_3761_; 
v_a_boxed_3760_ = lean_unbox(v_a_3752_);
v_res_3761_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3750_, v_e_3751_, v_a_boxed_3760_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_a_3754_);
lean_dec_ref(v_a_3753_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3762_, lean_object* v_00_u03b1_3763_, lean_object* v_c_3764_, lean_object* v_a_3765_, lean_object* v_b_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
uint8_t v_a_boxed_3775_; lean_object* v_res_3776_; 
v_a_boxed_3775_ = lean_unbox(v_a_3767_);
v_res_3776_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3762_, v_00_u03b1_3763_, v_c_3764_, v_a_3765_, v_b_3766_, v_a_boxed_3775_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3777_, lean_object* v_00_u03b1_3778_, lean_object* v_c_3779_, lean_object* v_inst_3780_, lean_object* v_a_3781_, lean_object* v_b_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
uint8_t v_a_boxed_3791_; lean_object* v_res_3792_; 
v_a_boxed_3791_ = lean_unbox(v_a_3783_);
v_res_3792_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3777_, v_00_u03b1_3778_, v_c_3779_, v_inst_3780_, v_a_3781_, v_b_3782_, v_a_boxed_3791_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
uint8_t v_a_boxed_3802_; lean_object* v_res_3803_; 
v_a_boxed_3802_ = lean_unbox(v_a_3794_);
v_res_3803_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3793_, v_a_boxed_3802_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
uint8_t v_a_boxed_3813_; lean_object* v_res_3814_; 
v_a_boxed_3813_ = lean_unbox(v_a_3805_);
v_res_3814_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3804_, v_a_boxed_3813_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3815_, lean_object* v_prop_3816_, lean_object* v_inst_3817_, lean_object* v_e_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
uint8_t v_a_boxed_3827_; lean_object* v_res_3828_; 
v_a_boxed_3827_ = lean_unbox(v_a_3819_);
v_res_3828_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3815_, v_prop_3816_, v_inst_3817_, v_e_3818_, v_a_boxed_3827_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3829_, lean_object* v_report_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
uint8_t v_report_boxed_3839_; uint8_t v_a_boxed_3840_; lean_object* v_res_3841_; 
v_report_boxed_3839_ = lean_unbox(v_report_3830_);
v_a_boxed_3840_ = lean_unbox(v_a_3831_);
v_res_3841_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3829_, v_report_boxed_3839_, v_a_boxed_3840_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3842_, lean_object* v_prop_3843_, lean_object* v_h_3844_, lean_object* v_e_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
uint8_t v_a_boxed_3854_; lean_object* v_res_3855_; 
v_a_boxed_3854_ = lean_unbox(v_a_3846_);
v_res_3855_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3842_, v_prop_3843_, v_h_3844_, v_e_3845_, v_a_boxed_3854_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_3856_, lean_object* v_a_3857_, lean_object* v___x_3858_, lean_object* v_snd_3859_, lean_object* v___x_3860_, lean_object* v_fst_3861_, lean_object* v_____r_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
uint8_t v___x_62111__boxed_3871_; uint8_t v___y_62113__boxed_3872_; lean_object* v_res_3873_; 
v___x_62111__boxed_3871_ = lean_unbox(v___x_3860_);
v___y_62113__boxed_3872_ = lean_unbox(v___y_3863_);
v_res_3873_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_3856_, v_a_3857_, v___x_3858_, v_snd_3859_, v___x_62111__boxed_3871_, v_fst_3861_, v_____r_3862_, v___y_62113__boxed_3872_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_a_3857_);
lean_dec_ref(v___x_3856_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
uint8_t v_a_boxed_3883_; lean_object* v_res_3884_; 
v_a_boxed_3883_ = lean_unbox(v_a_3875_);
v_res_3884_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3874_, v_a_boxed_3883_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
uint8_t v_a_boxed_3894_; lean_object* v_res_3895_; 
v_a_boxed_3894_ = lean_unbox(v_a_3886_);
v_res_3895_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_3885_, v_a_boxed_3894_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3896_, lean_object* v___x_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v___y_62323__boxed_3908_; lean_object* v_res_3909_; 
v___y_62323__boxed_3908_ = lean_unbox(v___y_3900_);
v_res_3909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3896_, v___x_3897_, v_a_3898_, v_b_3899_, v___y_62323__boxed_3908_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec_ref(v___x_3897_);
lean_dec(v_upperBound_3896_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3910_, lean_object* v_prop_3911_, lean_object* v_h_3912_, lean_object* v_e_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
uint8_t v_a_boxed_3922_; lean_object* v_res_3923_; 
v_a_boxed_3922_ = lean_unbox(v_a_3914_);
v_res_3923_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3910_, v_prop_3911_, v_h_3912_, v_e_3913_, v_a_boxed_3922_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___y_62436__boxed_3936_; lean_object* v_res_3937_; 
v___y_62436__boxed_3936_ = lean_unbox(v___y_3928_);
v_res_3937_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_3924_, v_x_3925_, v_x_3926_, v_x_3927_, v___y_62436__boxed_3936_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
uint8_t v_a_boxed_3947_; lean_object* v_res_3948_; 
v_a_boxed_3947_ = lean_unbox(v_a_3939_);
v_res_3948_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3938_, v_a_boxed_3947_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3949_, uint8_t v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3949_, v___y_3956_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v___y_64971__boxed_3968_; lean_object* v_res_3969_; 
v___y_64971__boxed_3968_ = lean_unbox(v___y_3960_);
v_res_3969_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3959_, v___y_64971__boxed_3968_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_3970_, uint8_t v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_3970_, v___y_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
uint8_t v___y_64997__boxed_3989_; lean_object* v_res_3990_; 
v___y_64997__boxed_3989_ = lean_unbox(v___y_3981_);
v_res_3990_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_3980_, v___y_64997__boxed_3989_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object* v_00_u03b1_3991_, lean_object* v_name_3992_, lean_object* v_type_3993_, lean_object* v_val_3994_, lean_object* v_k_3995_, uint8_t v_nondep_3996_, uint8_t v_kind_3997_, uint8_t v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_3992_, v_type_3993_, v_val_3994_, v_k_3995_, v_nondep_3996_, v_kind_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object* v_00_u03b1_4007_, lean_object* v_name_4008_, lean_object* v_type_4009_, lean_object* v_val_4010_, lean_object* v_k_4011_, lean_object* v_nondep_4012_, lean_object* v_kind_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
uint8_t v_nondep_boxed_4022_; uint8_t v_kind_boxed_4023_; uint8_t v___y_65023__boxed_4024_; lean_object* v_res_4025_; 
v_nondep_boxed_4022_ = lean_unbox(v_nondep_4012_);
v_kind_boxed_4023_ = lean_unbox(v_kind_4013_);
v___y_65023__boxed_4024_ = lean_unbox(v___y_4014_);
v_res_4025_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(v_00_u03b1_4007_, v_name_4008_, v_type_4009_, v_val_4010_, v_k_4011_, v_nondep_boxed_4022_, v_kind_boxed_4023_, v___y_65023__boxed_4024_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object* v_00_u03b1_4026_, lean_object* v_name_4027_, uint8_t v_bi_4028_, lean_object* v_type_4029_, lean_object* v_k_4030_, uint8_t v_kind_4031_, uint8_t v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_4027_, v_bi_4028_, v_type_4029_, v_k_4030_, v_kind_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object* v_00_u03b1_4041_, lean_object* v_name_4042_, lean_object* v_bi_4043_, lean_object* v_type_4044_, lean_object* v_k_4045_, lean_object* v_kind_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
uint8_t v_bi_boxed_4055_; uint8_t v_kind_boxed_4056_; uint8_t v___y_65049__boxed_4057_; lean_object* v_res_4058_; 
v_bi_boxed_4055_ = lean_unbox(v_bi_4043_);
v_kind_boxed_4056_ = lean_unbox(v_kind_4046_);
v___y_65049__boxed_4057_ = lean_unbox(v___y_4047_);
v_res_4058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(v_00_u03b1_4041_, v_name_4042_, v_bi_boxed_4055_, v_type_4044_, v_k_4045_, v_kind_boxed_4056_, v___y_65049__boxed_4057_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4059_, lean_object* v_m_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4060_, v_a_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4063_, lean_object* v_m_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4063_, v_m_4064_, v_a_4065_);
lean_dec_ref(v_a_4065_);
lean_dec_ref(v_m_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4067_, lean_object* v_m_4068_, lean_object* v_a_4069_, lean_object* v_b_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4068_, v_a_4069_, v_b_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4072_, lean_object* v_msg_4073_, uint8_t v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4072_, v_msg_4073_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4083_, lean_object* v_msg_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
uint8_t v___y_65079__boxed_4093_; lean_object* v_res_4094_; 
v___y_65079__boxed_4093_ = lean_unbox(v___y_4085_);
v_res_4094_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4083_, v_msg_4084_, v___y_65079__boxed_4093_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_inst_4098_, lean_object* v_R_4099_, lean_object* v_a_4100_, lean_object* v_b_4101_, lean_object* v_c_4102_, uint8_t v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4095_, v___x_4097_, v_a_4100_, v_b_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4112_, lean_object* v___x_4113_, lean_object* v___x_4114_, lean_object* v_inst_4115_, lean_object* v_R_4116_, lean_object* v_a_4117_, lean_object* v_b_4118_, lean_object* v_c_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
uint8_t v___y_65109__boxed_4128_; lean_object* v_res_4129_; 
v___y_65109__boxed_4128_ = lean_unbox(v___y_4120_);
v_res_4129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4112_, v___x_4113_, v___x_4114_, v_inst_4115_, v_R_4116_, v_a_4117_, v_b_4118_, v_c_4119_, v___y_65109__boxed_4128_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___x_4114_);
lean_dec(v___x_4113_);
lean_dec(v_upperBound_4112_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4130_, lean_object* v_a_4131_, lean_object* v_x_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4131_, v_x_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4134_, lean_object* v_a_4135_, lean_object* v_x_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4134_, v_a_4135_, v_x_4136_);
lean_dec(v_x_4136_);
lean_dec_ref(v_a_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4138_, lean_object* v_a_4139_, lean_object* v_x_4140_){
_start:
{
uint8_t v___x_4141_; 
v___x_4141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4139_, v_x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4142_, lean_object* v_a_4143_, lean_object* v_x_4144_){
_start:
{
uint8_t v_res_4145_; lean_object* v_r_4146_; 
v_res_4145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4142_, v_a_4143_, v_x_4144_);
lean_dec(v_x_4144_);
lean_dec_ref(v_a_4143_);
v_r_4146_ = lean_box(v_res_4145_);
return v_r_4146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4147_, lean_object* v_data_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4150_, lean_object* v_a_4151_, lean_object* v_b_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4151_, v_b_4152_, v_x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object* v_00_u03b2_4155_, lean_object* v_i_4156_, lean_object* v_source_4157_, lean_object* v_target_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v_i_4156_, v_source_4157_, v_target_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object* v_00_u03b2_4160_, lean_object* v_x_4161_, lean_object* v_x_4162_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_x_4161_, v_x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4164_, lean_object* v_i_4165_, lean_object* v_arg_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4164_, v_i_4165_, v_arg_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4188_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4188_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4188_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint8_t v___x_4177_; 
v___x_4177_ = lean_unbox(v_a_4173_);
lean_dec(v_a_4173_);
if (v___x_4177_ == 3)
{
uint8_t v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4178_ = 0;
v___x_4179_ = lean_box(v___x_4178_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4179_);
v___x_4181_ = v___x_4175_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
else
{
uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___x_4183_ = 1;
v___x_4184_ = lean_box(v___x_4183_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4184_);
v___x_4186_ = v___x_4175_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
v_a_4189_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4172_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4172_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4197_, lean_object* v_i_4198_, lean_object* v_arg_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4197_, v_i_4198_, v_arg_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_i_4198_);
lean_dec_ref(v_pinfos_4197_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4206_, lean_object* v_opts_4207_, lean_object* v_act_4208_, lean_object* v_decl_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_inc(v___y_4215_);
lean_inc_ref(v___y_4214_);
lean_inc(v___y_4213_);
lean_inc_ref(v___y_4212_);
lean_inc(v___y_4211_);
lean_inc_ref(v___y_4210_);
v___x_4217_ = lean_apply_6(v_act_4208_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
v___x_4218_ = l_Lean_profileitIOUnsafe___redArg(v_category_4206_, v_opts_4207_, v___x_4217_, v_decl_4209_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4219_, lean_object* v_opts_4220_, lean_object* v_act_4221_, lean_object* v_decl_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4219_, v_opts_4220_, v_act_4221_, v_decl_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v_opts_4220_);
lean_dec_ref(v_category_4219_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4231_, lean_object* v_category_4232_, lean_object* v_opts_4233_, lean_object* v_act_4234_, lean_object* v_decl_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4232_, v_opts_4233_, v_act_4234_, v_decl_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4244_, lean_object* v_category_4245_, lean_object* v_opts_4246_, lean_object* v_act_4247_, lean_object* v_decl_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4244_, v_category_4245_, v_opts_4246_, v_act_4247_, v_decl_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec_ref(v_opts_4246_);
lean_dec_ref(v_category_4245_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4257_, lean_object* v_e_4258_, uint8_t v___x_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___y_4268_; lean_object* v___x_4277_; uint8_t v_transparency_4278_; uint8_t v___x_4279_; 
v___x_4277_ = l_Lean_Meta_Context_config(v___y_4262_);
v_transparency_4278_ = lean_ctor_get_uint8(v___x_4277_, 9);
lean_dec_ref(v___x_4277_);
v___x_4279_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4278_, v___x_4257_);
if (v___x_4279_ == 0)
{
lean_object* v_keyedConfig_4280_; uint8_t v_trackZetaDelta_4281_; lean_object* v_zetaDeltaSet_4282_; lean_object* v_lctx_4283_; lean_object* v_localInstances_4284_; lean_object* v_defEqCtx_x3f_4285_; lean_object* v_synthPendingDepth_4286_; lean_object* v_customCanUnfoldPredicate_x3f_4287_; uint8_t v_univApprox_4288_; uint8_t v_inTypeClassResolution_4289_; uint8_t v_cacheInferType_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v_keyedConfig_4280_ = lean_ctor_get(v___y_4262_, 0);
v_trackZetaDelta_4281_ = lean_ctor_get_uint8(v___y_4262_, sizeof(void*)*7);
v_zetaDeltaSet_4282_ = lean_ctor_get(v___y_4262_, 1);
v_lctx_4283_ = lean_ctor_get(v___y_4262_, 2);
v_localInstances_4284_ = lean_ctor_get(v___y_4262_, 3);
v_defEqCtx_x3f_4285_ = lean_ctor_get(v___y_4262_, 4);
v_synthPendingDepth_4286_ = lean_ctor_get(v___y_4262_, 5);
v_customCanUnfoldPredicate_x3f_4287_ = lean_ctor_get(v___y_4262_, 6);
v_univApprox_4288_ = lean_ctor_get_uint8(v___y_4262_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4289_ = lean_ctor_get_uint8(v___y_4262_, sizeof(void*)*7 + 2);
v_cacheInferType_4290_ = lean_ctor_get_uint8(v___y_4262_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4280_);
v___x_4291_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4257_, v_keyedConfig_4280_);
lean_inc(v_customCanUnfoldPredicate_x3f_4287_);
lean_inc(v_synthPendingDepth_4286_);
lean_inc(v_defEqCtx_x3f_4285_);
lean_inc_ref(v_localInstances_4284_);
lean_inc_ref(v_lctx_4283_);
lean_inc(v_zetaDeltaSet_4282_);
v___x_4292_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
lean_ctor_set(v___x_4292_, 1, v_zetaDeltaSet_4282_);
lean_ctor_set(v___x_4292_, 2, v_lctx_4283_);
lean_ctor_set(v___x_4292_, 3, v_localInstances_4284_);
lean_ctor_set(v___x_4292_, 4, v_defEqCtx_x3f_4285_);
lean_ctor_set(v___x_4292_, 5, v_synthPendingDepth_4286_);
lean_ctor_set(v___x_4292_, 6, v_customCanUnfoldPredicate_x3f_4287_);
lean_ctor_set_uint8(v___x_4292_, sizeof(void*)*7, v_trackZetaDelta_4281_);
lean_ctor_set_uint8(v___x_4292_, sizeof(void*)*7 + 1, v_univApprox_4288_);
lean_ctor_set_uint8(v___x_4292_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4289_);
lean_ctor_set_uint8(v___x_4292_, sizeof(void*)*7 + 3, v_cacheInferType_4290_);
v___x_4293_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4258_, v___x_4259_, v___y_4260_, v___y_4261_, v___x_4292_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec_ref_known(v___x_4292_, 7);
v___y_4268_ = v___x_4293_;
goto v___jp_4267_;
}
else
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4258_, v___x_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
v___y_4268_ = v___x_4294_;
goto v___jp_4267_;
}
v___jp_4267_:
{
if (lean_obj_tag(v___y_4268_) == 0)
{
return v___y_4268_;
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
v_a_4269_ = lean_ctor_get(v___y_4268_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___y_4268_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___y_4268_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___y_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4295_, lean_object* v_e_4296_, lean_object* v___x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
uint8_t v___x_2103__boxed_4305_; uint8_t v___x_2104__boxed_4306_; lean_object* v_res_4307_; 
v___x_2103__boxed_4305_ = lean_unbox(v___x_4295_);
v___x_2104__boxed_4306_ = lean_unbox(v___x_4297_);
v_res_4307_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2103__boxed_4305_, v_e_4296_, v___x_2104__boxed_4306_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_toCold_4317_; lean_object* v_options_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_toCold_4317_ = lean_ctor_get(v_a_4314_, 0);
v_options_4318_ = lean_ctor_get(v_toCold_4317_, 2);
v___x_4319_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4320_ = 0;
v___x_4321_ = 2;
v___x_4322_ = lean_box(v___x_4321_);
v___x_4323_ = lean_box(v___x_4320_);
v___f_4324_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4324_, 0, v___x_4322_);
lean_closure_set(v___f_4324_, 1, v_e_4309_);
lean_closure_set(v___f_4324_, 2, v___x_4323_);
v___x_4325_ = lean_box(0);
v___x_4326_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4319_, v_options_4318_, v___f_4324_, v___x_4325_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_Meta_Sym_canon(v_e_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
return v_res_4335_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
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
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
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
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
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

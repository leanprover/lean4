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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_290_; 
lean_inc_ref(v_e_281_);
v___x_290_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_281_, v_a_283_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_Expr_cleanupAnnotations(v_a_291_);
v___x_293_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v___x_292_);
lean_dec_ref(v_e_281_);
goto v___jp_287_;
}
else
{
lean_object* v_arg_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_arg_294_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_294_);
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_e_281_);
goto v___jp_287_;
}
else
{
lean_object* v_arg_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_arg_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref(v_arg_297_);
v___x_298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_299_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0));
v___x_300_ = l_Lean_Expr_isConstOf(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_Expr_isApp(v___x_298_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_298_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_e_281_);
goto v___jp_287_;
}
else
{
lean_object* v_arg_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_arg_302_ = lean_ctor_get(v___x_298_, 1);
lean_inc_ref(v_arg_302_);
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_298_);
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
lean_dec_ref(v_arg_297_);
v___x_306_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_303_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_294_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_303_, v___x_308_);
lean_dec_ref(v___x_303_);
if (v___x_309_ == 0)
{
lean_dec_ref(v_e_281_);
goto v___jp_287_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec_ref(v___x_303_);
lean_dec_ref(v_e_281_);
v___x_311_ = l_Lean_Meta_getNatValue_x3f(v_arg_302_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_302_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_374_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_374_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_374_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_374_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
if (lean_obj_tag(v_a_312_) == 1)
{
lean_object* v_val_316_; lean_object* v___x_317_; 
lean_del_object(v___x_314_);
v_val_316_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_val_316_);
lean_dec_ref_known(v_a_312_, 1);
v___x_317_ = l_Lean_Meta_getNatValue_x3f(v_arg_294_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_294_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_361_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_361_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_361_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_361_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
if (lean_obj_tag(v_a_318_) == 1)
{
lean_object* v_val_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_356_; 
v_val_322_ = lean_ctor_get(v_a_318_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_356_ == 0)
{
v___x_324_ = v_a_318_;
v_isShared_325_ = v_isSharedCheck_356_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_val_322_);
lean_dec(v_a_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_356_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_nat_dec_eq(v_val_316_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_del_object(v___x_320_);
v___x_328_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6);
lean_inc(v_val_316_);
v___x_329_ = l_Lean_mkNatLit(v_val_316_);
v___x_330_ = l_Lean_Expr_app___override(v___x_328_, v___x_329_);
v___x_331_ = lean_nat_mod(v_val_322_, v_val_316_);
lean_dec(v_val_316_);
lean_dec(v_val_322_);
v___x_332_ = l_Lean_Meta_mkNumeral(v___x_330_, v___x_331_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_343_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_343_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_a_333_);
v___x_338_ = v___x_324_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_338_);
v___x_340_ = v___x_335_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_del_object(v___x_324_);
v_a_344_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_332_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_332_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
lean_del_object(v___x_324_);
lean_dec(v_val_322_);
lean_dec(v_val_316_);
v___x_352_ = lean_box(0);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_352_);
v___x_354_ = v___x_320_;
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
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_a_318_);
lean_dec(v_val_316_);
v___x_357_ = lean_box(0);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_357_);
v___x_359_ = v___x_320_;
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
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_val_316_);
v_a_362_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_317_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_317_);
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
lean_object* v___x_370_; lean_object* v___x_372_; 
lean_dec(v_a_312_);
lean_dec_ref(v_arg_294_);
v___x_370_ = lean_box(0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_370_);
v___x_372_ = v___x_314_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
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
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_arg_294_);
v_a_375_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_311_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_311_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_e_281_);
lean_inc_ref(v_arg_302_);
v___x_383_ = l_Lean_Meta_getLitValueModulus_x3f(v_arg_302_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_445_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_445_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_445_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_445_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
if (lean_obj_tag(v_a_384_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_389_; 
v_val_388_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_a_384_, 1);
v___x_389_ = l_Lean_Meta_getNatValue_x3f(v_arg_297_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_arg_297_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_432_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_432_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_432_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_432_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
if (lean_obj_tag(v_a_390_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_386_);
v_val_399_ = lean_ctor_get(v_a_390_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_390_);
if (v_isSharedCheck_427_ == 0)
{
v___x_401_ = v_a_390_;
v_isShared_402_ = v_isSharedCheck_427_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v_a_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_427_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_nat_dec_eq(v_val_388_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; 
v___x_405_ = lean_nat_dec_lt(v_val_399_, v_val_388_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_del_object(v___x_392_);
v___x_406_ = lean_nat_mod(v_val_399_, v_val_388_);
lean_dec(v_val_388_);
lean_dec(v_val_399_);
v___x_407_ = l_Lean_Meta_mkNumeral(v_arg_302_, v___x_406_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_418_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_a_408_);
v___x_413_ = v___x_401_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
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
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_del_object(v___x_401_);
v_a_419_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_407_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_407_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_del_object(v___x_401_);
lean_dec(v_val_399_);
lean_dec(v_val_388_);
lean_dec_ref(v_arg_302_);
goto v___jp_394_;
}
}
else
{
lean_del_object(v___x_401_);
lean_dec(v_val_399_);
lean_dec(v_val_388_);
lean_dec_ref(v_arg_302_);
goto v___jp_394_;
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_del_object(v___x_392_);
lean_dec(v_a_390_);
lean_dec(v_val_388_);
lean_dec_ref(v_arg_302_);
v___x_428_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_428_);
v___x_430_ = v___x_386_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
v___jp_394_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_box(0);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_val_388_);
lean_del_object(v___x_386_);
lean_dec_ref(v_arg_302_);
v_a_433_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_389_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_389_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec(v_a_384_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_297_);
v___x_441_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_441_);
v___x_443_ = v___x_386_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
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
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_297_);
v_a_446_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_383_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_383_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
else
{
lean_object* v___x_454_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_294_);
v___x_454_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_e_281_);
v_a_455_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_290_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_290_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
v___jp_287_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_472_, lean_object* v_k_473_, uint8_t v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_474_ == 0)
{
lean_object* v___x_484_; lean_object* v_canon_485_; lean_object* v_cache_486_; lean_object* v___x_487_; 
v___x_484_ = lean_st_ref_get(v_a_476_);
v_canon_485_ = lean_ctor_get(v___x_484_, 9);
lean_inc_ref(v_canon_485_);
lean_dec(v___x_484_);
v_cache_486_ = lean_ctor_get(v_canon_485_, 0);
lean_inc_ref(v_cache_486_);
lean_dec_ref(v_canon_485_);
lean_inc_ref(v_e_472_);
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_482_, v___x_483_, v_cache_486_, v_e_472_);
lean_dec_ref(v_cache_486_);
if (lean_obj_tag(v___x_487_) == 1)
{
lean_object* v_val_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_k_473_);
lean_dec_ref(v_e_472_);
v_val_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_val_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 0);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_val_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_487_);
v___x_496_ = lean_box(v_a_474_);
lean_inc(v_a_480_);
lean_inc_ref(v_a_479_);
lean_inc(v_a_478_);
lean_inc_ref(v_a_477_);
lean_inc(v_a_476_);
lean_inc_ref(v_a_475_);
v___x_497_ = lean_apply_8(v_k_473_, v___x_496_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, lean_box(0));
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_536_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_536_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_536_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_536_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v_canon_503_; lean_object* v_share_504_; lean_object* v_maxFVar_505_; lean_object* v_proofInstInfo_506_; lean_object* v_inferType_507_; lean_object* v_getLevel_508_; lean_object* v_congrInfo_509_; lean_object* v_defEqI_510_; lean_object* v_extensions_511_; lean_object* v_issues_512_; lean_object* v_instanceOverrides_513_; uint8_t v_debug_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_535_; 
v___x_502_ = lean_st_ref_take(v_a_476_);
v_canon_503_ = lean_ctor_get(v___x_502_, 9);
v_share_504_ = lean_ctor_get(v___x_502_, 0);
v_maxFVar_505_ = lean_ctor_get(v___x_502_, 1);
v_proofInstInfo_506_ = lean_ctor_get(v___x_502_, 2);
v_inferType_507_ = lean_ctor_get(v___x_502_, 3);
v_getLevel_508_ = lean_ctor_get(v___x_502_, 4);
v_congrInfo_509_ = lean_ctor_get(v___x_502_, 5);
v_defEqI_510_ = lean_ctor_get(v___x_502_, 6);
v_extensions_511_ = lean_ctor_get(v___x_502_, 7);
v_issues_512_ = lean_ctor_get(v___x_502_, 8);
v_instanceOverrides_513_ = lean_ctor_get(v___x_502_, 10);
v_debug_514_ = lean_ctor_get_uint8(v___x_502_, sizeof(void*)*11);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_535_ == 0)
{
v___x_516_ = v___x_502_;
v_isShared_517_ = v_isSharedCheck_535_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_instanceOverrides_513_);
lean_inc(v_canon_503_);
lean_inc(v_issues_512_);
lean_inc(v_extensions_511_);
lean_inc(v_defEqI_510_);
lean_inc(v_congrInfo_509_);
lean_inc(v_getLevel_508_);
lean_inc(v_inferType_507_);
lean_inc(v_proofInstInfo_506_);
lean_inc(v_maxFVar_505_);
lean_inc(v_share_504_);
lean_dec(v___x_502_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_535_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_cache_518_; lean_object* v_cacheInType_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_534_; 
v_cache_518_ = lean_ctor_get(v_canon_503_, 0);
v_cacheInType_519_ = lean_ctor_get(v_canon_503_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_canon_503_);
if (v_isSharedCheck_534_ == 0)
{
v___x_521_ = v_canon_503_;
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_cacheInType_519_);
lean_inc(v_cache_518_);
lean_dec(v_canon_503_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_inc(v_a_498_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_482_, v___x_483_, v_cache_518_, v_e_472_, v_a_498_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_cacheInType_519_);
v___x_525_ = v_reuseFailAlloc_533_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 9, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_share_504_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_maxFVar_505_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_proofInstInfo_506_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_inferType_507_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_getLevel_508_);
lean_ctor_set(v_reuseFailAlloc_532_, 5, v_congrInfo_509_);
lean_ctor_set(v_reuseFailAlloc_532_, 6, v_defEqI_510_);
lean_ctor_set(v_reuseFailAlloc_532_, 7, v_extensions_511_);
lean_ctor_set(v_reuseFailAlloc_532_, 8, v_issues_512_);
lean_ctor_set(v_reuseFailAlloc_532_, 9, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_532_, 10, v_instanceOverrides_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*11, v_debug_514_);
v___x_527_ = v_reuseFailAlloc_532_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_st_ref_put(v_a_476_, v___x_527_);
if (v_isShared_501_ == 0)
{
v___x_530_ = v___x_500_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_498_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_497_;
}
}
}
else
{
lean_object* v___x_537_; lean_object* v_canon_538_; lean_object* v_cacheInType_539_; lean_object* v___x_540_; 
v___x_537_ = lean_st_ref_get(v_a_476_);
v_canon_538_ = lean_ctor_get(v___x_537_, 9);
lean_inc_ref(v_canon_538_);
lean_dec(v___x_537_);
v_cacheInType_539_ = lean_ctor_get(v_canon_538_, 1);
lean_inc_ref(v_cacheInType_539_);
lean_dec_ref(v_canon_538_);
lean_inc_ref(v_e_472_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_482_, v___x_483_, v_cacheInType_539_, v_e_472_);
lean_dec_ref(v_cacheInType_539_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_k_473_);
lean_dec_ref(v_e_472_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_540_);
v___x_549_ = lean_box(v_a_474_);
lean_inc(v_a_480_);
lean_inc_ref(v_a_479_);
lean_inc(v_a_478_);
lean_inc_ref(v_a_477_);
lean_inc(v_a_476_);
lean_inc_ref(v_a_475_);
v___x_550_ = lean_apply_8(v_k_473_, v___x_549_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, lean_box(0));
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_589_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_589_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_589_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_589_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_canon_556_; lean_object* v_share_557_; lean_object* v_maxFVar_558_; lean_object* v_proofInstInfo_559_; lean_object* v_inferType_560_; lean_object* v_getLevel_561_; lean_object* v_congrInfo_562_; lean_object* v_defEqI_563_; lean_object* v_extensions_564_; lean_object* v_issues_565_; lean_object* v_instanceOverrides_566_; uint8_t v_debug_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_588_; 
v___x_555_ = lean_st_ref_take(v_a_476_);
v_canon_556_ = lean_ctor_get(v___x_555_, 9);
v_share_557_ = lean_ctor_get(v___x_555_, 0);
v_maxFVar_558_ = lean_ctor_get(v___x_555_, 1);
v_proofInstInfo_559_ = lean_ctor_get(v___x_555_, 2);
v_inferType_560_ = lean_ctor_get(v___x_555_, 3);
v_getLevel_561_ = lean_ctor_get(v___x_555_, 4);
v_congrInfo_562_ = lean_ctor_get(v___x_555_, 5);
v_defEqI_563_ = lean_ctor_get(v___x_555_, 6);
v_extensions_564_ = lean_ctor_get(v___x_555_, 7);
v_issues_565_ = lean_ctor_get(v___x_555_, 8);
v_instanceOverrides_566_ = lean_ctor_get(v___x_555_, 10);
v_debug_567_ = lean_ctor_get_uint8(v___x_555_, sizeof(void*)*11);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_588_ == 0)
{
v___x_569_ = v___x_555_;
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_instanceOverrides_566_);
lean_inc(v_canon_556_);
lean_inc(v_issues_565_);
lean_inc(v_extensions_564_);
lean_inc(v_defEqI_563_);
lean_inc(v_congrInfo_562_);
lean_inc(v_getLevel_561_);
lean_inc(v_inferType_560_);
lean_inc(v_proofInstInfo_559_);
lean_inc(v_maxFVar_558_);
lean_inc(v_share_557_);
lean_dec(v___x_555_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_cache_571_; lean_object* v_cacheInType_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_587_; 
v_cache_571_ = lean_ctor_get(v_canon_556_, 0);
v_cacheInType_572_ = lean_ctor_get(v_canon_556_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_canon_556_);
if (v_isSharedCheck_587_ == 0)
{
v___x_574_ = v_canon_556_;
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_cacheInType_572_);
lean_inc(v_cache_571_);
lean_dec(v_canon_556_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_a_551_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_482_, v___x_483_, v_cacheInType_572_, v_e_472_, v_a_551_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_cache_571_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_586_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 9, v___x_578_);
v___x_580_ = v___x_569_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_share_557_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_maxFVar_558_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_proofInstInfo_559_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_inferType_560_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_getLevel_561_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v_congrInfo_562_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_defEqI_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_extensions_564_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_issues_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 9, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 10, v_instanceOverrides_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*11, v_debug_567_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_st_ref_put(v_a_476_, v___x_580_);
if (v_isShared_554_ == 0)
{
v___x_583_ = v___x_553_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_551_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_590_, lean_object* v_k_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_a_boxed_600_; lean_object* v_res_601_; 
v_a_boxed_600_ = lean_unbox(v_a_592_);
v_res_601_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_590_, v_k_591_, v_a_boxed_600_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_601_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = l_Lean_Expr_cleanupAnnotations(v_e_608_);
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_611_ = l_Lean_Expr_isConstOf(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_612_ == 0)
{
lean_dec_ref(v___x_609_);
return v___x_612_;
}
else
{
lean_object* v_arg_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_arg_613_ = lean_ctor_get(v___x_609_, 1);
lean_inc_ref(v_arg_613_);
v___x_614_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_615_ = l_Lean_Expr_isApp(v___x_614_);
if (v___x_615_ == 0)
{
lean_dec_ref(v___x_614_);
lean_dec_ref(v_arg_613_);
return v___x_615_;
}
else
{
lean_object* v_arg_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_arg_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc_ref(v_arg_616_);
v___x_617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_614_);
v___x_618_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_617_);
lean_dec_ref(v_arg_616_);
lean_dec_ref(v_arg_613_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_621_ = l_Lean_Expr_isConstOf(v___x_619_, v___x_620_);
lean_dec_ref(v___x_619_);
if (v___x_621_ == 0)
{
lean_dec_ref(v_arg_616_);
lean_dec_ref(v_arg_613_);
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_Expr_isBoolTrue(v_arg_616_);
if (v___x_622_ == 0)
{
lean_dec_ref(v_arg_613_);
return v___x_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_Expr_isBoolTrue(v_arg_613_);
return v___x_623_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_609_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_624_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = l_Lean_Expr_cleanupAnnotations(v_e_630_);
v___x_632_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_633_ = l_Lean_Expr_isConstOf(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = l_Lean_Expr_isApp(v___x_631_);
if (v___x_634_ == 0)
{
lean_dec_ref(v___x_631_);
return v___x_634_;
}
else
{
lean_object* v_arg_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_arg_635_ = lean_ctor_get(v___x_631_, 1);
lean_inc_ref(v_arg_635_);
v___x_636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_631_);
v___x_637_ = l_Lean_Expr_isApp(v___x_636_);
if (v___x_637_ == 0)
{
lean_dec_ref(v___x_636_);
lean_dec_ref(v_arg_635_);
return v___x_637_;
}
else
{
lean_object* v_arg_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_arg_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc_ref(v_arg_638_);
v___x_639_ = l_Lean_Expr_appFnCleanup___redArg(v___x_636_);
v___x_640_ = l_Lean_Expr_isApp(v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v___x_639_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_635_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_639_);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_643_ = l_Lean_Expr_isConstOf(v___x_641_, v___x_642_);
lean_dec_ref(v___x_641_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_635_);
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_Expr_isBoolFalse(v_arg_638_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_arg_635_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = l_Lean_Expr_isBoolTrue(v_arg_635_);
return v___x_645_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_631_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_649_){
_start:
{
switch(v_x_649_)
{
case 0:
{
lean_object* v___x_650_; 
v___x_650_ = lean_unsigned_to_nat(0u);
return v___x_650_;
}
case 1:
{
lean_object* v___x_651_; 
v___x_651_ = lean_unsigned_to_nat(1u);
return v___x_651_;
}
case 2:
{
lean_object* v___x_652_; 
v___x_652_ = lean_unsigned_to_nat(2u);
return v___x_652_;
}
default: 
{
lean_object* v___x_653_; 
v___x_653_ = lean_unsigned_to_nat(3u);
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_654_){
_start:
{
uint8_t v_x_boxed_655_; lean_object* v_res_656_; 
v_x_boxed_655_ = lean_unbox(v_x_654_);
v_res_656_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_657_){
_start:
{
lean_inc(v_k_657_);
return v_k_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_658_);
lean_dec(v_k_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_660_, lean_object* v_ctorIdx_661_, uint8_t v_t_662_, lean_object* v_h_663_, lean_object* v_k_664_){
_start:
{
lean_inc(v_k_664_);
return v_k_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_665_, lean_object* v_ctorIdx_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_k_669_){
_start:
{
uint8_t v_t_boxed_670_; lean_object* v_res_671_; 
v_t_boxed_670_ = lean_unbox(v_t_667_);
v_res_671_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_665_, v_ctorIdx_666_, v_t_boxed_670_, v_h_668_, v_k_669_);
lean_dec(v_k_669_);
lean_dec(v_ctorIdx_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_672_){
_start:
{
lean_inc(v_canonType_672_);
return v_canonType_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_673_);
lean_dec(v_canonType_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_675_, uint8_t v_t_676_, lean_object* v_h_677_, lean_object* v_canonType_678_){
_start:
{
lean_inc(v_canonType_678_);
return v_canonType_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_canonType_682_){
_start:
{
uint8_t v_t_boxed_683_; lean_object* v_res_684_; 
v_t_boxed_683_ = lean_unbox(v_t_680_);
v_res_684_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_679_, v_t_boxed_683_, v_h_681_, v_canonType_682_);
lean_dec(v_canonType_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_685_){
_start:
{
lean_inc(v_canonInst_685_);
return v_canonInst_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_686_);
lean_dec(v_canonInst_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_688_, uint8_t v_t_689_, lean_object* v_h_690_, lean_object* v_canonInst_691_){
_start:
{
lean_inc(v_canonInst_691_);
return v_canonInst_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_692_, lean_object* v_t_693_, lean_object* v_h_694_, lean_object* v_canonInst_695_){
_start:
{
uint8_t v_t_boxed_696_; lean_object* v_res_697_; 
v_t_boxed_696_ = lean_unbox(v_t_693_);
v_res_697_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_692_, v_t_boxed_696_, v_h_694_, v_canonInst_695_);
lean_dec(v_canonInst_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_698_){
_start:
{
lean_inc(v_canonImplicit_698_);
return v_canonImplicit_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_699_);
lean_dec(v_canonImplicit_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_701_, uint8_t v_t_702_, lean_object* v_h_703_, lean_object* v_canonImplicit_704_){
_start:
{
lean_inc(v_canonImplicit_704_);
return v_canonImplicit_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_705_, lean_object* v_t_706_, lean_object* v_h_707_, lean_object* v_canonImplicit_708_){
_start:
{
uint8_t v_t_boxed_709_; lean_object* v_res_710_; 
v_t_boxed_709_ = lean_unbox(v_t_706_);
v_res_710_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_705_, v_t_boxed_709_, v_h_707_, v_canonImplicit_708_);
lean_dec(v_canonImplicit_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_711_){
_start:
{
lean_inc(v_visit_711_);
return v_visit_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_712_);
lean_dec(v_visit_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_714_, uint8_t v_t_715_, lean_object* v_h_716_, lean_object* v_visit_717_){
_start:
{
lean_inc(v_visit_717_);
return v_visit_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_visit_721_){
_start:
{
uint8_t v_t_boxed_722_; lean_object* v_res_723_; 
v_t_boxed_722_ = lean_unbox(v_t_719_);
v_res_723_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_718_, v_t_boxed_722_, v_h_720_, v_visit_721_);
lean_dec(v_visit_721_);
return v_res_723_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_738_, lean_object* v_x_739_){
_start:
{
switch(v_r_738_)
{
case 0:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_740_;
}
case 1:
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_741_;
}
case 2:
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_742_;
}
default: 
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_r_boxed_746_; lean_object* v_res_747_; 
v_r_boxed_746_ = lean_unbox(v_r_744_);
v_res_747_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_746_, v_x_745_);
lean_dec(v_x_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_750_, lean_object* v_i_751_, lean_object* v_arg_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_array_get_size(v_pinfos_750_);
v___x_809_ = lean_nat_dec_lt(v_i_751_, v___x_808_);
if (v___x_809_ == 0)
{
v___y_759_ = v_a_753_;
v___y_760_ = v_a_754_;
v___y_761_ = v_a_755_;
v___y_762_ = v_a_756_;
goto v___jp_758_;
}
else
{
lean_object* v_pinfo_810_; uint8_t v_isInstance_811_; 
v_pinfo_810_ = lean_array_fget_borrowed(v_pinfos_750_, v_i_751_);
v_isInstance_811_ = lean_ctor_get_uint8(v_pinfo_810_, sizeof(void*)*1 + 4);
if (v_isInstance_811_ == 0)
{
uint8_t v_isProp_812_; 
v_isProp_812_ = lean_ctor_get_uint8(v_pinfo_810_, sizeof(void*)*1 + 2);
if (v_isProp_812_ == 0)
{
uint8_t v___x_813_; 
v___x_813_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_810_);
if (v___x_813_ == 0)
{
v___y_759_ = v_a_753_;
v___y_760_ = v_a_754_;
v___y_761_ = v_a_755_;
v___y_762_ = v_a_756_;
goto v___jp_758_;
}
else
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_isTypeFormer(v_arg_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_830_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_830_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_830_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_830_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v___x_819_; 
v___x_819_ = lean_unbox(v_a_815_);
lean_dec(v_a_815_);
if (v___x_819_ == 0)
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_820_ = 2;
v___x_821_ = lean_box(v___x_820_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = 0;
v___x_826_ = lean_box(v___x_825_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_826_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_814_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_814_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
else
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_arg_752_);
v___x_839_ = 3;
v___x_840_ = lean_box(v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
else
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref(v_arg_752_);
v___x_842_ = 1;
v___x_843_ = lean_box(v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
v___jp_758_:
{
lean_object* v___x_763_; 
lean_inc_ref(v_arg_752_);
v___x_763_ = l_Lean_Meta_isProp(v_arg_752_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_799_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_799_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_799_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_799_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v___x_768_; 
v___x_768_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_del_object(v___x_766_);
v___x_769_ = l_Lean_Meta_isTypeFormer(v_arg_752_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_785_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_785_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_785_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint8_t v___x_774_; 
v___x_774_ = lean_unbox(v_a_770_);
lean_dec(v_a_770_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_775_ = 3;
v___x_776_ = lean_box(v___x_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = 0;
v___x_781_ = lean_box(v___x_780_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_781_);
v___x_783_ = v___x_772_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_769_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_769_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_dec_ref(v_arg_752_);
v___x_794_ = 3;
v___x_795_ = lean_box(v___x_794_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_795_);
v___x_797_ = v___x_766_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
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
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_arg_752_);
v_a_800_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_763_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_763_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_845_, lean_object* v_i_846_, lean_object* v_arg_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_845_, v_i_846_, v_arg_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_i_846_);
lean_dec_ref(v_pinfos_845_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_854_, lean_object* v_offset_855_){
_start:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_nat_dec_eq(v_offset_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = l_Lean_mkNatLit(v_offset_855_);
v___x_859_ = l_Lean_mkNatAdd(v_e_854_, v___x_858_);
return v___x_859_;
}
else
{
lean_dec(v_offset_855_);
return v_e_854_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_860_; lean_object* v_dummy_861_; 
v___x_860_ = lean_box(0);
v_dummy_861_ = l_Lean_Expr_sort___override(v___x_860_);
return v_dummy_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_862_, lean_object* v_e_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
uint8_t v_fromClass_869_; 
v_fromClass_869_ = lean_ctor_get_uint8(v_info_862_, sizeof(void*)*3);
if (v_fromClass_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_863_, v_fromClass_869_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_906_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_906_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_906_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_906_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_del_object(v___x_873_);
v_val_875_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v_a_871_, 1);
v___x_876_ = l_Lean_Expr_getAppFn(v_val_875_);
v___x_877_ = l_Lean_Meta_reduceProj_x3f(v___x_876_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
if (lean_obj_tag(v_a_878_) == 0)
{
lean_dec(v_val_875_);
return v___x_877_;
}
else
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_900_; 
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_901_);
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_val_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_899_; 
v_val_882_ = lean_ctor_get(v_a_878_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_878_);
if (v_isSharedCheck_899_ == 0)
{
v___x_884_ = v_a_878_;
v_isShared_885_ = v_isSharedCheck_899_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_val_882_);
lean_dec(v_a_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_899_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_dummy_886_; lean_object* v_nargs_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_dummy_886_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_887_ = l_Lean_Expr_getAppNumArgs(v_val_875_);
lean_inc(v_nargs_887_);
v___x_888_ = lean_mk_array(v_nargs_887_, v_dummy_886_);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_sub(v_nargs_887_, v___x_889_);
lean_dec(v_nargs_887_);
v___x_891_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_875_, v___x_888_, v___x_890_);
v___x_892_ = l_Lean_mkAppN(v_val_882_, v___x_891_);
lean_dec_ref(v___x_891_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_892_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_894_);
v___x_896_ = v___x_880_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
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
}
}
else
{
lean_dec(v_val_875_);
return v___x_877_;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_a_871_);
v___x_902_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_902_);
v___x_904_ = v___x_873_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
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
else
{
return v___x_870_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_e_863_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_909_, lean_object* v_e_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_909_, v_e_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec_ref(v_info_909_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_917_, lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_917_, v_e_918_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_927_, lean_object* v_e_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_927_, v_e_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_info_927_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_937_){
_start:
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_939_ = l_Lean_Expr_isConstOf(v_e_937_, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_940_);
lean_dec_ref(v_e_940_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = l_Lean_Expr_cleanupAnnotations(v_e_976_);
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_979_ = l_Lean_Expr_isConstOf(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
uint8_t v___x_980_; 
v___x_980_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_980_ == 0)
{
lean_dec_ref(v___x_977_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_977_);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_983_ = l_Lean_Expr_isConstOf(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_Expr_isApp(v___x_981_);
if (v___x_984_ == 0)
{
lean_dec_ref(v___x_981_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_981_);
v___x_986_ = l_Lean_Expr_isApp(v___x_985_);
if (v___x_986_ == 0)
{
lean_dec_ref(v___x_985_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_985_);
v___x_988_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___x_987_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
v___x_990_ = l_Lean_Expr_isApp(v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_989_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
return v___x_992_;
}
else
{
lean_object* v_arg_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_arg_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc_ref(v_arg_993_);
v___x_994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_996_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_998_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1000_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1002_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_1003_);
lean_dec_ref(v___x_994_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v_arg_993_);
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_993_);
lean_dec_ref(v_arg_993_);
return v___x_1005_;
}
}
else
{
uint8_t v___x_1006_; 
lean_dec_ref(v___x_994_);
v___x_1006_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_993_);
lean_dec_ref(v_arg_993_);
return v___x_1006_;
}
}
else
{
uint8_t v___x_1007_; 
lean_dec_ref(v___x_994_);
v___x_1007_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_993_);
lean_dec_ref(v_arg_993_);
return v___x_1007_;
}
}
else
{
uint8_t v___x_1008_; 
lean_dec_ref(v___x_994_);
v___x_1008_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_993_);
lean_dec_ref(v_arg_993_);
return v___x_1008_;
}
}
else
{
uint8_t v___x_1009_; 
lean_dec_ref(v___x_994_);
v___x_1009_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_993_);
lean_dec_ref(v_arg_993_);
return v___x_1009_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_981_);
return v___x_983_;
}
}
}
else
{
lean_dec_ref(v___x_977_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1019_, lean_object* v_inst_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
lean_inc_ref(v_inst_1020_);
lean_inc_ref(v_e_1019_);
v___x_1028_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1019_, v_inst_1020_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1079_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1079_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1079_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_del_object(v___x_1031_);
v___x_1034_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1019_);
v___x_1035_ = l_Lean_indentExpr(v_e_1019_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_indentExpr(v_inst_1020_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1021_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1067_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1067_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1067_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint8_t v_verbose_1046_; 
v_verbose_1046_ = lean_ctor_get_uint8(v_a_1042_, 0);
lean_dec(v_a_1042_);
if (v_verbose_1046_ == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref_known(v___x_1040_, 2);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_e_1019_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_e_1019_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
lean_object* v___x_1050_; 
lean_del_object(v___x_1044_);
v___x_1050_ = l_Lean_Meta_Sym_reportIssue(v___x_1040_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1058_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_e_1019_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_e_1019_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_e_1019_);
v_a_1059_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1050_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1050_);
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
lean_dec_ref_known(v___x_1040_, 2);
lean_dec_ref(v_e_1019_);
v_a_1068_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1041_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1041_);
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
else
{
lean_object* v___x_1077_; 
lean_dec_ref(v_e_1019_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_inst_1020_);
v___x_1077_ = v___x_1031_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_inst_1020_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_inst_1020_);
lean_dec_ref(v_e_1019_);
v_a_1080_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1028_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1028_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1088_, lean_object* v_inst_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1088_, v_inst_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v_res_1097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1101_, lean_object* v_type_1102_, uint8_t v_report_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; 
lean_inc_ref(v_type_1102_);
v___x_1111_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1102_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1163_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1163_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1163_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
if (lean_obj_tag(v_a_1112_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1117_; 
lean_del_object(v___x_1114_);
lean_dec_ref(v_type_1102_);
v_val_1116_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v_a_1112_, 1);
v___x_1117_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1101_, v_val_1116_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
return v___x_1117_;
}
else
{
lean_dec(v_a_1112_);
if (v_report_1103_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v_type_1102_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_e_1101_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_e_1101_);
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
lean_del_object(v___x_1114_);
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1101_);
v___x_1122_ = l_Lean_indentExpr(v_e_1101_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_indentExpr(v_type_1102_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1104_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1154_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1154_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1154_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v_verbose_1133_; 
v_verbose_1133_ = lean_ctor_get_uint8(v_a_1129_, 0);
lean_dec(v_a_1129_);
if (v_verbose_1133_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1127_, 2);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_e_1101_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_e_1101_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_object* v___x_1137_; 
lean_del_object(v___x_1131_);
v___x_1137_ = l_Lean_Meta_Sym_reportIssue(v___x_1127_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1137_, 0);
lean_dec(v_unused_1145_);
v___x_1139_ = v___x_1137_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_dec(v___x_1137_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_e_1101_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_e_1101_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_e_1101_);
v_a_1146_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1137_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1137_);
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
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref_known(v___x_1127_, 2);
lean_dec_ref(v_e_1101_);
v_a_1155_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1128_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1128_);
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
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_type_1102_);
lean_dec_ref(v_e_1101_);
v_a_1164_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1111_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1111_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1172_, lean_object* v_type_1173_, lean_object* v_report_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
uint8_t v_report_boxed_1182_; lean_object* v_res_1183_; 
v_report_boxed_1182_ = lean_unbox(v_report_1174_);
v_res_1183_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1172_, v_type_1173_, v_report_boxed_1182_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1184_, lean_object* v_type_1185_, uint8_t v_report_1186_, uint8_t v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1184_, v_type_1185_, v_report_1186_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1196_, lean_object* v_type_1197_, lean_object* v_report_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v_report_boxed_1207_; uint8_t v_a_boxed_1208_; lean_object* v_res_1209_; 
v_report_boxed_1207_ = lean_unbox(v_report_1198_);
v_a_boxed_1208_ = lean_unbox(v_a_1199_);
v_res_1209_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1196_, v_type_1197_, v_report_boxed_1207_, v_a_boxed_1208_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
else
{
lean_object* v_key_1213_; lean_object* v_tail_1214_; uint8_t v___x_1215_; 
v_key_1213_ = lean_ctor_get(v_x_1211_, 0);
v_tail_1214_ = lean_ctor_get(v_x_1211_, 2);
v___x_1215_ = lean_expr_eqv(v_key_1213_, v_a_1210_);
if (v___x_1215_ == 0)
{
v_x_1211_ = v_tail_1214_;
goto _start;
}
else
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1217_, lean_object* v_x_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1217_, v_x_1218_);
lean_dec(v_x_1218_);
lean_dec_ref(v_a_1217_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
return v_x_1221_;
}
else
{
lean_object* v_key_1223_; lean_object* v_value_1224_; lean_object* v_tail_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1248_; 
v_key_1223_ = lean_ctor_get(v_x_1222_, 0);
v_value_1224_ = lean_ctor_get(v_x_1222_, 1);
v_tail_1225_ = lean_ctor_get(v_x_1222_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1227_ = v_x_1222_;
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_tail_1225_);
lean_inc(v_value_1224_);
lean_inc(v_key_1223_);
lean_dec(v_x_1222_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v_fold_1233_; uint64_t v___x_1234_; uint64_t v___x_1235_; uint64_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1229_ = lean_array_get_size(v_x_1221_);
v___x_1230_ = l_Lean_Expr_hash(v_key_1223_);
v___x_1231_ = 32ULL;
v___x_1232_ = lean_uint64_shift_right(v___x_1230_, v___x_1231_);
v_fold_1233_ = lean_uint64_xor(v___x_1230_, v___x_1232_);
v___x_1234_ = 16ULL;
v___x_1235_ = lean_uint64_shift_right(v_fold_1233_, v___x_1234_);
v___x_1236_ = lean_uint64_xor(v_fold_1233_, v___x_1235_);
v___x_1237_ = lean_uint64_to_usize(v___x_1236_);
v___x_1238_ = lean_usize_of_nat(v___x_1229_);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_sub(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_usize_land(v___x_1237_, v___x_1240_);
v___x_1242_ = lean_array_uget_borrowed(v_x_1221_, v___x_1241_);
lean_inc(v___x_1242_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 2, v___x_1242_);
v___x_1244_ = v___x_1227_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_key_1223_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_value_1224_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_array_uset(v_x_1221_, v___x_1241_, v___x_1244_);
v_x_1221_ = v___x_1245_;
v_x_1222_ = v_tail_1225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object* v_i_1249_, lean_object* v_source_1250_, lean_object* v_target_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_source_1250_);
v___x_1253_ = lean_nat_dec_lt(v_i_1249_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_source_1250_);
lean_dec(v_i_1249_);
return v_target_1251_;
}
else
{
lean_object* v_es_1254_; lean_object* v___x_1255_; lean_object* v_source_1256_; lean_object* v_target_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_es_1254_ = lean_array_fget(v_source_1250_, v_i_1249_);
v___x_1255_ = lean_box(0);
v_source_1256_ = lean_array_fset(v_source_1250_, v_i_1249_, v___x_1255_);
v_target_1257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_target_1251_, v_es_1254_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_add(v_i_1249_, v___x_1258_);
lean_dec(v_i_1249_);
v_i_1249_ = v___x_1259_;
v_source_1250_ = v_source_1256_;
v_target_1251_ = v_target_1257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_nbuckets_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1262_ = lean_array_get_size(v_data_1261_);
v___x_1263_ = lean_unsigned_to_nat(2u);
v_nbuckets_1264_ = lean_nat_mul(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_mk_array(v_nbuckets_1264_, v___x_1266_);
v___x_1268_ = lean_array_propagate_mark(v_data_1261_, v___x_1267_);
v___x_1269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v___x_1265_, v_data_1261_, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1270_, lean_object* v_b_1271_, lean_object* v_x_1272_){
_start:
{
if (lean_obj_tag(v_x_1272_) == 0)
{
lean_dec(v_b_1271_);
lean_dec_ref(v_a_1270_);
return v_x_1272_;
}
else
{
lean_object* v_key_1273_; lean_object* v_value_1274_; lean_object* v_tail_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1287_; 
v_key_1273_ = lean_ctor_get(v_x_1272_, 0);
v_value_1274_ = lean_ctor_get(v_x_1272_, 1);
v_tail_1275_ = lean_ctor_get(v_x_1272_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_x_1272_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1277_ = v_x_1272_;
v_isShared_1278_ = v_isSharedCheck_1287_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_tail_1275_);
lean_inc(v_value_1274_);
lean_inc(v_key_1273_);
lean_dec(v_x_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1287_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_expr_eqv(v_key_1273_, v_a_1270_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1270_, v_b_1271_, v_tail_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 2, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_key_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_value_1274_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_value_1274_);
lean_dec(v_key_1273_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_b_1271_);
lean_ctor_set(v___x_1277_, 0, v_a_1270_);
v___x_1285_ = v___x_1277_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1270_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_b_1271_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_tail_1275_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1288_, lean_object* v_a_1289_, lean_object* v_b_1290_){
_start:
{
lean_object* v_size_1291_; lean_object* v_buckets_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1335_; 
v_size_1291_ = lean_ctor_get(v_m_1288_, 0);
v_buckets_1292_ = lean_ctor_get(v_m_1288_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_m_1288_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1294_ = v_m_1288_;
v_isShared_1295_ = v_isSharedCheck_1335_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_buckets_1292_);
lean_inc(v_size_1291_);
lean_dec(v_m_1288_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1335_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; uint64_t v___x_1297_; uint64_t v___x_1298_; uint64_t v___x_1299_; uint64_t v_fold_1300_; uint64_t v___x_1301_; uint64_t v___x_1302_; uint64_t v___x_1303_; size_t v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v_bkt_1309_; uint8_t v___x_1310_; 
v___x_1296_ = lean_array_get_size(v_buckets_1292_);
v___x_1297_ = l_Lean_Expr_hash(v_a_1289_);
v___x_1298_ = 32ULL;
v___x_1299_ = lean_uint64_shift_right(v___x_1297_, v___x_1298_);
v_fold_1300_ = lean_uint64_xor(v___x_1297_, v___x_1299_);
v___x_1301_ = 16ULL;
v___x_1302_ = lean_uint64_shift_right(v_fold_1300_, v___x_1301_);
v___x_1303_ = lean_uint64_xor(v_fold_1300_, v___x_1302_);
v___x_1304_ = lean_uint64_to_usize(v___x_1303_);
v___x_1305_ = lean_usize_of_nat(v___x_1296_);
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_sub(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_usize_land(v___x_1304_, v___x_1307_);
v_bkt_1309_ = lean_array_uget_borrowed(v_buckets_1292_, v___x_1308_);
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1289_, v_bkt_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v_size_x27_1312_; lean_object* v___x_1313_; lean_object* v_buckets_x27_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1311_ = lean_unsigned_to_nat(1u);
v_size_x27_1312_ = lean_nat_add(v_size_1291_, v___x_1311_);
lean_dec(v_size_1291_);
lean_inc(v_bkt_1309_);
v___x_1313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1289_);
lean_ctor_set(v___x_1313_, 1, v_b_1290_);
lean_ctor_set(v___x_1313_, 2, v_bkt_1309_);
v_buckets_x27_1314_ = lean_array_uset(v_buckets_1292_, v___x_1308_, v___x_1313_);
v___x_1315_ = lean_unsigned_to_nat(4u);
v___x_1316_ = lean_nat_mul(v_size_x27_1312_, v___x_1315_);
v___x_1317_ = lean_unsigned_to_nat(3u);
v___x_1318_ = lean_nat_div(v___x_1316_, v___x_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_array_get_size(v_buckets_x27_1314_);
v___x_1320_ = lean_nat_dec_le(v___x_1318_, v___x_1319_);
lean_dec(v___x_1318_);
if (v___x_1320_ == 0)
{
lean_object* v_val_1321_; lean_object* v___x_1323_; 
v_val_1321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1314_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v_val_1321_);
lean_ctor_set(v___x_1294_, 0, v_size_x27_1312_);
v___x_1323_ = v___x_1294_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_size_x27_1312_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_val_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
lean_object* v___x_1326_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v_buckets_x27_1314_);
lean_ctor_set(v___x_1294_, 0, v_size_x27_1312_);
v___x_1326_ = v___x_1294_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_size_x27_1312_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_buckets_x27_1314_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v_buckets_x27_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_inc(v_bkt_1309_);
v___x_1328_ = lean_box(0);
v_buckets_x27_1329_ = lean_array_uset(v_buckets_1292_, v___x_1308_, v___x_1328_);
v___x_1330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1289_, v_b_1290_, v_bkt_1309_);
v___x_1331_ = lean_array_uset(v_buckets_x27_1329_, v___x_1308_, v___x_1330_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v___x_1331_);
v___x_1333_ = v___x_1294_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_size_1291_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object* v_k_1336_, uint8_t v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(v___y_1337_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1347_ = lean_apply_9(v_k_1336_, v_b_1340_, v___x_1346_, v___y_1338_, v___y_1339_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, lean_box(0));
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object* v_k_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___y_61400__boxed_1358_; lean_object* v_res_1359_; 
v___y_61400__boxed_1358_ = lean_unbox(v___y_1349_);
v_res_1359_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1348_, v___y_61400__boxed_1358_, v___y_1350_, v___y_1351_, v_b_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object* v_name_1360_, uint8_t v_bi_1361_, lean_object* v_type_1362_, lean_object* v_k_1363_, uint8_t v_kind_1364_, uint8_t v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(v___y_1365_);
lean_inc(v___y_1367_);
lean_inc_ref(v___y_1366_);
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1374_, 0, v_k_1363_);
lean_closure_set(v___f_1374_, 1, v___x_1373_);
lean_closure_set(v___f_1374_, 2, v___y_1366_);
lean_closure_set(v___f_1374_, 3, v___y_1367_);
v___x_1375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1360_, v_bi_1361_, v_type_1362_, v___f_1374_, v_kind_1364_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object* v_name_1384_, lean_object* v_bi_1385_, lean_object* v_type_1386_, lean_object* v_k_1387_, lean_object* v_kind_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_bi_boxed_1397_; uint8_t v_kind_boxed_1398_; uint8_t v___y_61428__boxed_1399_; lean_object* v_res_1400_; 
v_bi_boxed_1397_ = lean_unbox(v_bi_1385_);
v_kind_boxed_1398_ = lean_unbox(v_kind_1388_);
v___y_61428__boxed_1399_ = lean_unbox(v___y_1389_);
v_res_1400_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1384_, v_bi_boxed_1397_, v_type_1386_, v_k_1387_, v_kind_boxed_1398_, v___y_61428__boxed_1399_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = l_Lean_Meta_isMatcherCore(v_env_1405_, v_declName_1401_);
v___x_1407_ = lean_box(v___x_1406_);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1409_, v___y_1410_);
lean_dec(v___y_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v_env_1420_; lean_object* v___x_1421_; lean_object* v_toCold_1422_; lean_object* v_mctx_1423_; lean_object* v_lctx_1424_; lean_object* v_options_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1419_ = lean_st_ref_get(v___y_1417_);
v_env_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_env_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = lean_st_ref_get(v___y_1415_);
v_toCold_1422_ = lean_ctor_get(v___y_1416_, 0);
v_mctx_1423_ = lean_ctor_get(v___x_1421_, 0);
lean_inc_ref(v_mctx_1423_);
lean_dec(v___x_1421_);
v_lctx_1424_ = lean_ctor_get(v___y_1414_, 2);
v_options_1425_ = lean_ctor_get(v_toCold_1422_, 2);
lean_inc_ref(v_options_1425_);
lean_inc_ref(v_lctx_1424_);
v___x_1426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1426_, 0, v_env_1420_);
lean_ctor_set(v___x_1426_, 1, v_mctx_1423_);
lean_ctor_set(v___x_1426_, 2, v_lctx_1424_);
lean_ctor_set(v___x_1426_, 3, v_options_1425_);
v___x_1427_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v_msgData_1413_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1436_; double v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_float_of_nat(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1441_, lean_object* v_msg_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_ref_1448_; lean_object* v___x_1449_; lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1495_; 
v_ref_1448_ = lean_ctor_get(v___y_1445_, 2);
v___x_1449_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1495_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1495_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v_traceState_1455_; lean_object* v_env_1456_; lean_object* v_nextMacroScope_1457_; lean_object* v_ngen_1458_; lean_object* v_auxDeclNGen_1459_; lean_object* v_cache_1460_; lean_object* v_recordedDeps_1461_; lean_object* v_messages_1462_; lean_object* v_infoState_1463_; lean_object* v_snapshotTasks_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1494_; 
v___x_1454_ = lean_st_ref_take(v___y_1446_);
v_traceState_1455_ = lean_ctor_get(v___x_1454_, 4);
v_env_1456_ = lean_ctor_get(v___x_1454_, 0);
v_nextMacroScope_1457_ = lean_ctor_get(v___x_1454_, 1);
v_ngen_1458_ = lean_ctor_get(v___x_1454_, 2);
v_auxDeclNGen_1459_ = lean_ctor_get(v___x_1454_, 3);
v_cache_1460_ = lean_ctor_get(v___x_1454_, 5);
v_recordedDeps_1461_ = lean_ctor_get(v___x_1454_, 6);
v_messages_1462_ = lean_ctor_get(v___x_1454_, 7);
v_infoState_1463_ = lean_ctor_get(v___x_1454_, 8);
v_snapshotTasks_1464_ = lean_ctor_get(v___x_1454_, 9);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1466_ = v___x_1454_;
v_isShared_1467_ = v_isSharedCheck_1494_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snapshotTasks_1464_);
lean_inc(v_infoState_1463_);
lean_inc(v_messages_1462_);
lean_inc(v_recordedDeps_1461_);
lean_inc(v_cache_1460_);
lean_inc(v_traceState_1455_);
lean_inc(v_auxDeclNGen_1459_);
lean_inc(v_ngen_1458_);
lean_inc(v_nextMacroScope_1457_);
lean_inc(v_env_1456_);
lean_dec(v___x_1454_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1494_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
uint64_t v_tid_1468_; lean_object* v_traces_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1493_; 
v_tid_1468_ = lean_ctor_get_uint64(v_traceState_1455_, sizeof(void*)*1);
v_traces_1469_ = lean_ctor_get(v_traceState_1455_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_traceState_1455_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1471_ = v_traceState_1455_;
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_traces_1469_);
lean_dec(v_traceState_1455_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; double v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1476_ = 0;
v___x_1477_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1478_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1478_, 0, v_cls_1441_);
lean_ctor_set(v___x_1478_, 1, v___x_1474_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
lean_ctor_set_float(v___x_1478_, sizeof(void*)*3, v___x_1475_);
lean_ctor_set_float(v___x_1478_, sizeof(void*)*3 + 8, v___x_1475_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*3 + 16, v___x_1476_);
v___x_1479_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1480_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v_a_1450_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
lean_inc(v_ref_1448_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_ref_1448_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_PersistentArray_push___redArg(v_traces_1469_, v___x_1481_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1482_);
v___x_1484_ = v___x_1471_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1482_);
lean_ctor_set_uint64(v_reuseFailAlloc_1492_, sizeof(void*)*1, v_tid_1468_);
v___x_1484_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 4, v___x_1484_);
v___x_1486_ = v___x_1466_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_env_1456_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_nextMacroScope_1457_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_ngen_1458_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_auxDeclNGen_1459_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1491_, 5, v_cache_1460_);
lean_ctor_set(v_reuseFailAlloc_1491_, 6, v_recordedDeps_1461_);
lean_ctor_set(v_reuseFailAlloc_1491_, 7, v_messages_1462_);
lean_ctor_set(v_reuseFailAlloc_1491_, 8, v_infoState_1463_);
lean_ctor_set(v_reuseFailAlloc_1491_, 9, v_snapshotTasks_1464_);
v___x_1486_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_st_ref_put(v___y_1446_, v___x_1486_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1473_);
v___x_1489_ = v___x_1452_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1473_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1496_, lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1496_, v_msg_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
else
{
lean_object* v_key_1507_; lean_object* v_value_1508_; lean_object* v_tail_1509_; uint8_t v___x_1510_; 
v_key_1507_ = lean_ctor_get(v_x_1505_, 0);
v_value_1508_ = lean_ctor_get(v_x_1505_, 1);
v_tail_1509_ = lean_ctor_get(v_x_1505_, 2);
v___x_1510_ = lean_expr_eqv(v_key_1507_, v_a_1504_);
if (v___x_1510_ == 0)
{
v_x_1505_ = v_tail_1509_;
goto _start;
}
else
{
lean_object* v___x_1512_; 
lean_inc(v_value_1508_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_value_1508_);
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1513_, v_x_1514_);
lean_dec(v_x_1514_);
lean_dec_ref(v_a_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_buckets_1518_; lean_object* v___x_1519_; uint64_t v___x_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v_fold_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; uint64_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_buckets_1518_ = lean_ctor_get(v_m_1516_, 1);
v___x_1519_ = lean_array_get_size(v_buckets_1518_);
v___x_1520_ = l_Lean_Expr_hash(v_a_1517_);
v___x_1521_ = 32ULL;
v___x_1522_ = lean_uint64_shift_right(v___x_1520_, v___x_1521_);
v_fold_1523_ = lean_uint64_xor(v___x_1520_, v___x_1522_);
v___x_1524_ = 16ULL;
v___x_1525_ = lean_uint64_shift_right(v_fold_1523_, v___x_1524_);
v___x_1526_ = lean_uint64_xor(v_fold_1523_, v___x_1525_);
v___x_1527_ = lean_uint64_to_usize(v___x_1526_);
v___x_1528_ = lean_usize_of_nat(v___x_1519_);
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_sub(v___x_1528_, v___x_1529_);
v___x_1531_ = lean_usize_land(v___x_1527_, v___x_1530_);
v___x_1532_ = lean_array_uget_borrowed(v_buckets_1518_, v___x_1531_);
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1517_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1534_, v_a_1535_);
lean_dec_ref(v_a_1535_);
lean_dec_ref(v_m_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_env_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = lean_st_ref_get(v___y_1538_);
v_env_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_env_1541_);
lean_dec(v___x_1540_);
v___x_1542_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1541_, v_declName_1537_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1544_, v___y_1545_);
lean_dec(v___y_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object* v_name_1548_, lean_object* v_type_1549_, lean_object* v_val_1550_, lean_object* v_k_1551_, uint8_t v_nondep_1552_, uint8_t v_kind_1553_, uint8_t v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(v___y_1554_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1563_, 0, v_k_1551_);
lean_closure_set(v___f_1563_, 1, v___x_1562_);
lean_closure_set(v___f_1563_, 2, v___y_1555_);
lean_closure_set(v___f_1563_, 3, v___y_1556_);
v___x_1564_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1548_, v_type_1549_, v_val_1550_, v___f_1563_, v_nondep_1552_, v_kind_1553_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1564_) == 0)
{
return v___x_1564_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object* v_name_1573_, lean_object* v_type_1574_, lean_object* v_val_1575_, lean_object* v_k_1576_, lean_object* v_nondep_1577_, lean_object* v_kind_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_nondep_boxed_1587_; uint8_t v_kind_boxed_1588_; uint8_t v___y_61675__boxed_1589_; lean_object* v_res_1590_; 
v_nondep_boxed_1587_ = lean_unbox(v_nondep_1577_);
v_kind_boxed_1588_ = lean_unbox(v_kind_1578_);
v___y_61675__boxed_1589_ = lean_unbox(v___y_1579_);
v_res_1590_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1573_, v_type_1574_, v_val_1575_, v_k_1576_, v_nondep_boxed_1587_, v_kind_boxed_1588_, v___y_61675__boxed_1589_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = l_Lean_instInhabitedExpr;
v___x_1593_ = lean_panic_fn_borrowed(v___x_1592_, v_msg_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1594_, lean_object* v_body_1595_, lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v___y_61844__boxed_1605_; lean_object* v_res_1606_; 
v___y_61844__boxed_1605_ = lean_unbox(v___y_1597_);
v_res_1606_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1594_, v_body_1595_, v_x_1596_, v___y_61844__boxed_1605_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1609_, lean_object* v_body_1610_, lean_object* v_x_1611_, uint8_t v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_array_push(v_fvars_1609_, v_x_1611_);
v___x_1621_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1620_, v_body_1610_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1622_, lean_object* v_body_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v___y_61855__boxed_1633_; lean_object* v_res_1634_; 
v___y_61855__boxed_1633_ = lean_unbox(v___y_1625_);
v_res_1634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1622_, v_body_1623_, v_x_1624_, v___y_61855__boxed_1633_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1635_, lean_object* v_e_1636_, uint8_t v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
if (lean_obj_tag(v_e_1636_) == 6)
{
lean_object* v_binderName_1645_; lean_object* v_binderType_1646_; lean_object* v_body_1647_; uint8_t v_binderInfo_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_binderName_1645_ = lean_ctor_get(v_e_1636_, 0);
lean_inc(v_binderName_1645_);
v_binderType_1646_ = lean_ctor_get(v_e_1636_, 1);
lean_inc_ref(v_binderType_1646_);
v_body_1647_ = lean_ctor_get(v_e_1636_, 2);
lean_inc_ref(v_body_1647_);
v_binderInfo_1648_ = lean_ctor_get_uint8(v_e_1636_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1636_, 3);
lean_inc_ref(v_fvars_1635_);
v___f_1649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1649_, 0, v_fvars_1635_);
lean_closure_set(v___f_1649_, 1, v_body_1647_);
v___x_1650_ = lean_expr_instantiate_rev(v_binderType_1646_, v_fvars_1635_);
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_binderType_1646_);
v___x_1651_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1650_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = 0;
v___x_1654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_1645_, v_binderInfo_1648_, v_a_1652_, v___f_1649_, v___x_1653_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1654_;
}
else
{
lean_dec_ref(v___f_1649_);
lean_dec(v_binderName_1645_);
return v___x_1651_;
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_expr_instantiate_rev(v_e_1636_, v_fvars_1635_);
lean_dec_ref(v_e_1636_);
v___x_1656_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1655_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; uint8_t v___x_1658_; uint8_t v___x_1659_; uint8_t v___x_1660_; lean_object* v___x_1661_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = 0;
v___x_1659_ = 1;
v___x_1660_ = 1;
v___x_1661_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1635_, v_a_1657_, v___x_1658_, v___x_1659_, v___x_1658_, v___x_1659_, v___x_1660_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec_ref(v_fvars_1635_);
return v___x_1661_;
}
else
{
lean_dec_ref(v_fvars_1635_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1662_, uint8_t v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
if (v_a_1663_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1672_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1671_, v_e_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1674_ = l_Lean_Meta_Sym_etaReduce(v_e_1662_);
lean_dec_ref(v_e_1662_);
v___x_1675_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1673_, v___x_1674_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1676_, lean_object* v_body_1677_, lean_object* v_x_1678_, uint8_t v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_array_push(v_fvars_1676_, v_x_1678_);
v___x_1688_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1687_, v_body_1677_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1689_, lean_object* v_body_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___y_61866__boxed_1700_; lean_object* v_res_1701_; 
v___y_61866__boxed_1700_ = lean_unbox(v___y_1692_);
v_res_1701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1689_, v_body_1690_, v_x_1691_, v___y_61866__boxed_1700_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1702_, lean_object* v_e_1703_, uint8_t v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
if (lean_obj_tag(v_e_1703_) == 8)
{
lean_object* v_declName_1712_; lean_object* v_type_1713_; lean_object* v_value_1714_; lean_object* v_body_1715_; uint8_t v_nondep_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_declName_1712_ = lean_ctor_get(v_e_1703_, 0);
lean_inc(v_declName_1712_);
v_type_1713_ = lean_ctor_get(v_e_1703_, 1);
lean_inc_ref(v_type_1713_);
v_value_1714_ = lean_ctor_get(v_e_1703_, 2);
lean_inc_ref(v_value_1714_);
v_body_1715_ = lean_ctor_get(v_e_1703_, 3);
lean_inc_ref(v_body_1715_);
v_nondep_1716_ = lean_ctor_get_uint8(v_e_1703_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1703_, 4);
lean_inc_ref(v_fvars_1702_);
v___f_1717_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1717_, 0, v_fvars_1702_);
lean_closure_set(v___f_1717_, 1, v_body_1715_);
v___x_1718_ = lean_expr_instantiate_rev(v_type_1713_, v_fvars_1702_);
lean_dec_ref(v_type_1713_);
v___x_1719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1718_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_expr_instantiate_rev(v_value_1714_, v_fvars_1702_);
lean_dec_ref(v_fvars_1702_);
lean_dec_ref(v_value_1714_);
v___x_1722_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1721_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = 0;
v___x_1725_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_declName_1712_, v_a_1720_, v_a_1723_, v___f_1717_, v_nondep_1716_, v___x_1724_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1725_;
}
else
{
lean_dec(v_a_1720_);
lean_dec_ref(v___f_1717_);
lean_dec(v_declName_1712_);
return v___x_1722_;
}
}
else
{
lean_dec_ref(v___f_1717_);
lean_dec_ref(v_value_1714_);
lean_dec(v_declName_1712_);
lean_dec_ref(v_fvars_1702_);
return v___x_1719_;
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_expr_instantiate_rev(v_e_1703_, v_fvars_1702_);
lean_dec_ref(v_e_1703_);
v___x_1727_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1726_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; uint8_t v___x_1729_; uint8_t v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = 1;
v___x_1730_ = 0;
v___x_1731_ = 1;
v___x_1732_ = l_Lean_Meta_mkLetFVars(v_fvars_1702_, v_a_1728_, v___x_1729_, v___x_1730_, v___x_1731_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec_ref(v_fvars_1702_);
return v___x_1732_;
}
else
{
lean_dec_ref(v_fvars_1702_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1733_, uint8_t v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
if (v_a_1734_ == 0)
{
uint8_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = 1;
v___x_1743_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1733_, v___x_1742_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1745_, uint8_t v_report_1746_, uint8_t v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
lean_inc(v_a_1753_);
lean_inc_ref(v_a_1752_);
lean_inc(v_a_1751_);
lean_inc_ref(v_a_1750_);
lean_inc_ref(v_e_1745_);
v___x_1755_ = lean_infer_type(v_e_1745_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc_n(v_a_1756_, 2);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = l_Lean_Meta_isProp(v_a_1756_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1770_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
if (v_a_1747_ == 0)
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1766_ == 0)
{
lean_del_object(v___x_1760_);
goto v___jp_1762_;
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_a_1756_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_e_1745_);
v___x_1768_ = v___x_1760_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_e_1745_);
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
lean_del_object(v___x_1760_);
lean_dec(v_a_1758_);
goto v___jp_1762_;
}
v___jp_1762_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1756_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1745_, v_a_1764_, v_report_1746_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
return v___x_1765_;
}
else
{
lean_dec_ref(v_e_1745_);
return v___x_1763_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1756_);
lean_dec_ref(v_e_1745_);
v_a_1771_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1757_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1757_);
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
lean_dec_ref(v_e_1745_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1779_, uint8_t v_report_1780_, uint8_t v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
if (v_a_1781_ == 0)
{
lean_object* v___x_1789_; lean_object* v_canon_1790_; lean_object* v_cache_1791_; lean_object* v___x_1792_; 
v___x_1789_ = lean_st_ref_get(v_a_1783_);
v_canon_1790_ = lean_ctor_get(v___x_1789_, 9);
lean_inc_ref(v_canon_1790_);
lean_dec(v___x_1789_);
v_cache_1791_ = lean_ctor_get(v_canon_1790_, 0);
lean_inc_ref(v_cache_1791_);
lean_dec_ref(v_canon_1790_);
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1791_, v_e_1779_);
lean_dec_ref(v_cache_1791_);
if (lean_obj_tag(v___x_1792_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_e_1779_);
v_val_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_val_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 0);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_val_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1801_; 
lean_dec(v___x_1792_);
lean_inc_ref(v_e_1779_);
v___x_1801_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1779_, v_report_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1840_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1840_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1840_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v_canon_1807_; lean_object* v_share_1808_; lean_object* v_maxFVar_1809_; lean_object* v_proofInstInfo_1810_; lean_object* v_inferType_1811_; lean_object* v_getLevel_1812_; lean_object* v_congrInfo_1813_; lean_object* v_defEqI_1814_; lean_object* v_extensions_1815_; lean_object* v_issues_1816_; lean_object* v_instanceOverrides_1817_; uint8_t v_debug_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1839_; 
v___x_1806_ = lean_st_ref_take(v_a_1783_);
v_canon_1807_ = lean_ctor_get(v___x_1806_, 9);
v_share_1808_ = lean_ctor_get(v___x_1806_, 0);
v_maxFVar_1809_ = lean_ctor_get(v___x_1806_, 1);
v_proofInstInfo_1810_ = lean_ctor_get(v___x_1806_, 2);
v_inferType_1811_ = lean_ctor_get(v___x_1806_, 3);
v_getLevel_1812_ = lean_ctor_get(v___x_1806_, 4);
v_congrInfo_1813_ = lean_ctor_get(v___x_1806_, 5);
v_defEqI_1814_ = lean_ctor_get(v___x_1806_, 6);
v_extensions_1815_ = lean_ctor_get(v___x_1806_, 7);
v_issues_1816_ = lean_ctor_get(v___x_1806_, 8);
v_instanceOverrides_1817_ = lean_ctor_get(v___x_1806_, 10);
v_debug_1818_ = lean_ctor_get_uint8(v___x_1806_, sizeof(void*)*11);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1820_ = v___x_1806_;
v_isShared_1821_ = v_isSharedCheck_1839_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_instanceOverrides_1817_);
lean_inc(v_canon_1807_);
lean_inc(v_issues_1816_);
lean_inc(v_extensions_1815_);
lean_inc(v_defEqI_1814_);
lean_inc(v_congrInfo_1813_);
lean_inc(v_getLevel_1812_);
lean_inc(v_inferType_1811_);
lean_inc(v_proofInstInfo_1810_);
lean_inc(v_maxFVar_1809_);
lean_inc(v_share_1808_);
lean_dec(v___x_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1839_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_cache_1822_; lean_object* v_cacheInType_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1838_; 
v_cache_1822_ = lean_ctor_get(v_canon_1807_, 0);
v_cacheInType_1823_ = lean_ctor_get(v_canon_1807_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_canon_1807_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1825_ = v_canon_1807_;
v_isShared_1826_ = v_isSharedCheck_1838_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_cacheInType_1823_);
lean_inc(v_cache_1822_);
lean_dec(v_canon_1807_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1838_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_inc(v_a_1802_);
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1822_, v_e_1779_, v_a_1802_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_cacheInType_1823_);
v___x_1829_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 9, v___x_1829_);
v___x_1831_ = v___x_1820_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_share_1808_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_maxFVar_1809_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_proofInstInfo_1810_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_inferType_1811_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_getLevel_1812_);
lean_ctor_set(v_reuseFailAlloc_1836_, 5, v_congrInfo_1813_);
lean_ctor_set(v_reuseFailAlloc_1836_, 6, v_defEqI_1814_);
lean_ctor_set(v_reuseFailAlloc_1836_, 7, v_extensions_1815_);
lean_ctor_set(v_reuseFailAlloc_1836_, 8, v_issues_1816_);
lean_ctor_set(v_reuseFailAlloc_1836_, 9, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1836_, 10, v_instanceOverrides_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*11, v_debug_1818_);
v___x_1831_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_st_ref_put(v_a_1783_, v___x_1831_);
if (v_isShared_1805_ == 0)
{
v___x_1834_ = v___x_1804_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1802_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1779_);
return v___x_1801_;
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v_canon_1842_; lean_object* v_cacheInType_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_st_ref_get(v_a_1783_);
v_canon_1842_ = lean_ctor_get(v___x_1841_, 9);
lean_inc_ref(v_canon_1842_);
lean_dec(v___x_1841_);
v_cacheInType_1843_ = lean_ctor_get(v_canon_1842_, 1);
lean_inc_ref(v_cacheInType_1843_);
lean_dec_ref(v_canon_1842_);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1843_, v_e_1779_);
lean_dec_ref(v_cacheInType_1843_);
if (lean_obj_tag(v___x_1844_) == 1)
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v_e_1779_);
v_val_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_val_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v___x_1853_; 
lean_dec(v___x_1844_);
lean_inc_ref(v_e_1779_);
v___x_1853_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1779_, v_report_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1892_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1892_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1892_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v_canon_1859_; lean_object* v_share_1860_; lean_object* v_maxFVar_1861_; lean_object* v_proofInstInfo_1862_; lean_object* v_inferType_1863_; lean_object* v_getLevel_1864_; lean_object* v_congrInfo_1865_; lean_object* v_defEqI_1866_; lean_object* v_extensions_1867_; lean_object* v_issues_1868_; lean_object* v_instanceOverrides_1869_; uint8_t v_debug_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1891_; 
v___x_1858_ = lean_st_ref_take(v_a_1783_);
v_canon_1859_ = lean_ctor_get(v___x_1858_, 9);
v_share_1860_ = lean_ctor_get(v___x_1858_, 0);
v_maxFVar_1861_ = lean_ctor_get(v___x_1858_, 1);
v_proofInstInfo_1862_ = lean_ctor_get(v___x_1858_, 2);
v_inferType_1863_ = lean_ctor_get(v___x_1858_, 3);
v_getLevel_1864_ = lean_ctor_get(v___x_1858_, 4);
v_congrInfo_1865_ = lean_ctor_get(v___x_1858_, 5);
v_defEqI_1866_ = lean_ctor_get(v___x_1858_, 6);
v_extensions_1867_ = lean_ctor_get(v___x_1858_, 7);
v_issues_1868_ = lean_ctor_get(v___x_1858_, 8);
v_instanceOverrides_1869_ = lean_ctor_get(v___x_1858_, 10);
v_debug_1870_ = lean_ctor_get_uint8(v___x_1858_, sizeof(void*)*11);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1872_ = v___x_1858_;
v_isShared_1873_ = v_isSharedCheck_1891_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_instanceOverrides_1869_);
lean_inc(v_canon_1859_);
lean_inc(v_issues_1868_);
lean_inc(v_extensions_1867_);
lean_inc(v_defEqI_1866_);
lean_inc(v_congrInfo_1865_);
lean_inc(v_getLevel_1864_);
lean_inc(v_inferType_1863_);
lean_inc(v_proofInstInfo_1862_);
lean_inc(v_maxFVar_1861_);
lean_inc(v_share_1860_);
lean_dec(v___x_1858_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1891_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_cache_1874_; lean_object* v_cacheInType_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1890_; 
v_cache_1874_ = lean_ctor_get(v_canon_1859_, 0);
v_cacheInType_1875_ = lean_ctor_get(v_canon_1859_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_canon_1859_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1877_ = v_canon_1859_;
v_isShared_1878_ = v_isSharedCheck_1890_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_cacheInType_1875_);
lean_inc(v_cache_1874_);
lean_dec(v_canon_1859_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1890_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_inc(v_a_1854_);
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1875_, v_e_1779_, v_a_1854_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 9, v___x_1881_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_share_1860_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_maxFVar_1861_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_proofInstInfo_1862_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_inferType_1863_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_getLevel_1864_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_congrInfo_1865_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_defEqI_1866_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_extensions_1867_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_issues_1868_);
lean_ctor_set(v_reuseFailAlloc_1888_, 9, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1888_, 10, v_instanceOverrides_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*11, v_debug_1870_);
v___x_1883_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_st_ref_put(v_a_1783_, v___x_1883_);
if (v_isShared_1857_ == 0)
{
v___x_1886_ = v___x_1856_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1854_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1779_);
return v___x_1853_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1909_ = l_Lean_mkConst(v___x_1908_, v___x_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1910_, lean_object* v_prop_1911_, lean_object* v_inst_1912_, lean_object* v_e_1913_, uint8_t v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1922_; 
lean_inc_ref(v_prop_1911_);
v___x_1922_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1911_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1965_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1965_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1965_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___y_1928_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1923_);
v___x_1934_ = l_Lean_Expr_app___override(v___x_1933_, v_a_1923_);
if (v_a_1914_ == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1934_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___y_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
if (lean_obj_tag(v_a_1936_) == 0)
{
lean_inc_ref(v_inst_1912_);
v___y_1938_ = v_inst_1912_;
goto v___jp_1937_;
}
else
{
lean_object* v_val_1954_; 
v_val_1954_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v_a_1936_, 1);
v___y_1938_ = v_val_1954_;
goto v___jp_1937_;
}
v___jp_1937_:
{
lean_object* v___x_1939_; 
lean_inc_ref(v_inst_1912_);
v___x_1939_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1912_, v___y_1938_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1953_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1953_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1953_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
size_t v___x_1944_; size_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_ptr_addr(v_prop_1911_);
lean_dec_ref(v_prop_1911_);
v___x_1945_ = lean_ptr_addr(v_a_1923_);
v___x_1946_ = lean_usize_dec_eq(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_del_object(v___x_1942_);
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_inst_1912_);
v___y_1928_ = v_a_1940_;
goto v___jp_1927_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_ptr_addr(v_inst_1912_);
lean_dec_ref(v_inst_1912_);
v___x_1948_ = lean_ptr_addr(v_a_1940_);
v___x_1949_ = lean_usize_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_del_object(v___x_1942_);
lean_dec_ref(v_e_1913_);
v___y_1928_ = v_a_1940_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1951_; 
lean_dec(v_a_1940_);
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
lean_dec_ref(v_g_1910_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v_e_1913_);
v___x_1951_ = v___x_1942_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_e_1913_);
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
}
else
{
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_inst_1912_);
lean_dec_ref(v_prop_1911_);
lean_dec_ref(v_g_1910_);
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_inst_1912_);
lean_dec_ref(v_prop_1911_);
lean_dec_ref(v_g_1910_);
v_a_1955_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1935_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1935_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
uint8_t v___x_1963_; lean_object* v___x_1964_; 
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_prop_1911_);
lean_dec_ref(v_g_1910_);
v___x_1963_ = 0;
v___x_1964_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1912_, v___x_1934_, v___x_1963_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
return v___x_1964_;
}
v___jp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_mkAppB(v_g_1910_, v_a_1923_, v___y_1928_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1929_);
v___x_1931_ = v___x_1925_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_inst_1912_);
lean_dec_ref(v_prop_1911_);
lean_dec_ref(v_g_1910_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1966_, lean_object* v_prop_1967_, lean_object* v_h_1968_, lean_object* v_e_1969_, uint8_t v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
if (v_a_1970_ == 0)
{
lean_object* v___x_1978_; lean_object* v_canon_1979_; lean_object* v_cache_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_st_ref_get(v_a_1972_);
v_canon_1979_ = lean_ctor_get(v___x_1978_, 9);
lean_inc_ref(v_canon_1979_);
lean_dec(v___x_1978_);
v_cache_1980_ = lean_ctor_get(v_canon_1979_, 0);
lean_inc_ref(v_cache_1980_);
lean_dec_ref(v_canon_1979_);
v___x_1981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1980_, v_e_1969_);
lean_dec_ref(v_cache_1980_);
if (lean_obj_tag(v___x_1981_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_h_1968_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
v_val_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 0);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_val_1982_);
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
lean_object* v___x_1990_; 
lean_dec(v___x_1981_);
lean_inc_ref(v_e_1969_);
v___x_1990_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1966_, v_prop_1967_, v_h_1968_, v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2029_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2029_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2029_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v_canon_1996_; lean_object* v_share_1997_; lean_object* v_maxFVar_1998_; lean_object* v_proofInstInfo_1999_; lean_object* v_inferType_2000_; lean_object* v_getLevel_2001_; lean_object* v_congrInfo_2002_; lean_object* v_defEqI_2003_; lean_object* v_extensions_2004_; lean_object* v_issues_2005_; lean_object* v_instanceOverrides_2006_; uint8_t v_debug_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2028_; 
v___x_1995_ = lean_st_ref_take(v_a_1972_);
v_canon_1996_ = lean_ctor_get(v___x_1995_, 9);
v_share_1997_ = lean_ctor_get(v___x_1995_, 0);
v_maxFVar_1998_ = lean_ctor_get(v___x_1995_, 1);
v_proofInstInfo_1999_ = lean_ctor_get(v___x_1995_, 2);
v_inferType_2000_ = lean_ctor_get(v___x_1995_, 3);
v_getLevel_2001_ = lean_ctor_get(v___x_1995_, 4);
v_congrInfo_2002_ = lean_ctor_get(v___x_1995_, 5);
v_defEqI_2003_ = lean_ctor_get(v___x_1995_, 6);
v_extensions_2004_ = lean_ctor_get(v___x_1995_, 7);
v_issues_2005_ = lean_ctor_get(v___x_1995_, 8);
v_instanceOverrides_2006_ = lean_ctor_get(v___x_1995_, 10);
v_debug_2007_ = lean_ctor_get_uint8(v___x_1995_, sizeof(void*)*11);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2009_ = v___x_1995_;
v_isShared_2010_ = v_isSharedCheck_2028_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_instanceOverrides_2006_);
lean_inc(v_canon_1996_);
lean_inc(v_issues_2005_);
lean_inc(v_extensions_2004_);
lean_inc(v_defEqI_2003_);
lean_inc(v_congrInfo_2002_);
lean_inc(v_getLevel_2001_);
lean_inc(v_inferType_2000_);
lean_inc(v_proofInstInfo_1999_);
lean_inc(v_maxFVar_1998_);
lean_inc(v_share_1997_);
lean_dec(v___x_1995_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2028_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_cache_2011_; lean_object* v_cacheInType_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2027_; 
v_cache_2011_ = lean_ctor_get(v_canon_1996_, 0);
v_cacheInType_2012_ = lean_ctor_get(v_canon_1996_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_canon_1996_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2014_ = v_canon_1996_;
v_isShared_2015_ = v_isSharedCheck_2027_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_cacheInType_2012_);
lean_inc(v_cache_2011_);
lean_dec(v_canon_1996_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2027_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_a_1991_);
v___x_2016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2011_, v_e_1969_, v_a_1991_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_cacheInType_2012_);
v___x_2018_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 9, v___x_2018_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_share_1997_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_maxFVar_1998_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_proofInstInfo_1999_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_inferType_2000_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_getLevel_2001_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v_congrInfo_2002_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_defEqI_2003_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_extensions_2004_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_issues_2005_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2025_, 10, v_instanceOverrides_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*11, v_debug_2007_);
v___x_2020_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_st_ref_put(v_a_1972_, v___x_2020_);
if (v_isShared_1994_ == 0)
{
v___x_2023_ = v___x_1993_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_1991_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1969_);
return v___x_1990_;
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v_canon_2031_; lean_object* v_cacheInType_2032_; lean_object* v___x_2033_; 
v___x_2030_ = lean_st_ref_get(v_a_1972_);
v_canon_2031_ = lean_ctor_get(v___x_2030_, 9);
lean_inc_ref(v_canon_2031_);
lean_dec(v___x_2030_);
v_cacheInType_2032_ = lean_ctor_get(v_canon_2031_, 1);
lean_inc_ref(v_cacheInType_2032_);
lean_dec_ref(v_canon_2031_);
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2032_, v_e_1969_);
lean_dec_ref(v_cacheInType_2032_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_h_1968_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_val_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 0);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_val_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec(v___x_2033_);
lean_inc_ref(v_e_1969_);
v___x_2042_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1966_, v_prop_1967_, v_h_1968_, v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2081_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2081_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2081_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v_canon_2048_; lean_object* v_share_2049_; lean_object* v_maxFVar_2050_; lean_object* v_proofInstInfo_2051_; lean_object* v_inferType_2052_; lean_object* v_getLevel_2053_; lean_object* v_congrInfo_2054_; lean_object* v_defEqI_2055_; lean_object* v_extensions_2056_; lean_object* v_issues_2057_; lean_object* v_instanceOverrides_2058_; uint8_t v_debug_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2080_; 
v___x_2047_ = lean_st_ref_take(v_a_1972_);
v_canon_2048_ = lean_ctor_get(v___x_2047_, 9);
v_share_2049_ = lean_ctor_get(v___x_2047_, 0);
v_maxFVar_2050_ = lean_ctor_get(v___x_2047_, 1);
v_proofInstInfo_2051_ = lean_ctor_get(v___x_2047_, 2);
v_inferType_2052_ = lean_ctor_get(v___x_2047_, 3);
v_getLevel_2053_ = lean_ctor_get(v___x_2047_, 4);
v_congrInfo_2054_ = lean_ctor_get(v___x_2047_, 5);
v_defEqI_2055_ = lean_ctor_get(v___x_2047_, 6);
v_extensions_2056_ = lean_ctor_get(v___x_2047_, 7);
v_issues_2057_ = lean_ctor_get(v___x_2047_, 8);
v_instanceOverrides_2058_ = lean_ctor_get(v___x_2047_, 10);
v_debug_2059_ = lean_ctor_get_uint8(v___x_2047_, sizeof(void*)*11);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2061_ = v___x_2047_;
v_isShared_2062_ = v_isSharedCheck_2080_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_instanceOverrides_2058_);
lean_inc(v_canon_2048_);
lean_inc(v_issues_2057_);
lean_inc(v_extensions_2056_);
lean_inc(v_defEqI_2055_);
lean_inc(v_congrInfo_2054_);
lean_inc(v_getLevel_2053_);
lean_inc(v_inferType_2052_);
lean_inc(v_proofInstInfo_2051_);
lean_inc(v_maxFVar_2050_);
lean_inc(v_share_2049_);
lean_dec(v___x_2047_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2080_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_cache_2063_; lean_object* v_cacheInType_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2079_; 
v_cache_2063_ = lean_ctor_get(v_canon_2048_, 0);
v_cacheInType_2064_ = lean_ctor_get(v_canon_2048_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_canon_2048_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2066_ = v_canon_2048_;
v_isShared_2067_ = v_isSharedCheck_2079_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_cacheInType_2064_);
lean_inc(v_cache_2063_);
lean_dec(v_canon_2048_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2079_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_inc(v_a_2043_);
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2064_, v_e_1969_, v_a_2043_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_cache_2063_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 9, v___x_2070_);
v___x_2072_ = v___x_2061_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_share_2049_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_maxFVar_2050_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_proofInstInfo_2051_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_inferType_2052_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_getLevel_2053_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v_congrInfo_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_defEqI_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_extensions_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_issues_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2077_, 10, v_instanceOverrides_2058_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*11, v_debug_2059_);
v___x_2072_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_st_ref_put(v_a_1972_, v___x_2072_);
if (v_isShared_2046_ == 0)
{
v___x_2075_ = v___x_2045_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2043_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1969_);
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2082_, lean_object* v_prop_2083_, lean_object* v_h_2084_, lean_object* v_e_2085_, uint8_t v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_a_2095_; lean_object* v___y_2129_; 
if (v_a_2086_ == 0)
{
lean_object* v___x_2169_; lean_object* v_canon_2170_; lean_object* v_cache_2171_; lean_object* v___x_2172_; 
v___x_2169_ = lean_st_ref_get(v_a_2088_);
v_canon_2170_ = lean_ctor_get(v___x_2169_, 9);
lean_inc_ref(v_canon_2170_);
lean_dec(v___x_2169_);
v_cache_2171_ = lean_ctor_get(v_canon_2170_, 0);
lean_inc_ref(v_cache_2171_);
lean_dec_ref(v_canon_2170_);
v___x_2172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2171_, v_e_2085_);
lean_dec_ref(v_cache_2171_);
if (lean_obj_tag(v___x_2172_) == 1)
{
lean_object* v_val_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_e_2085_);
lean_dec_ref(v_h_2084_);
lean_dec_ref(v_prop_2083_);
lean_dec_ref(v_g_2082_);
v_val_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_val_2173_);
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
lean_ctor_set_tag(v___x_2175_, 0);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_val_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
lean_object* v___x_2181_; 
lean_dec(v___x_2172_);
lean_inc_ref(v_prop_2083_);
v___x_2181_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2083_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_n(v_a_2182_, 2);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2183_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2182_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___y_2186_; lean_object* v___y_2189_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
if (lean_obj_tag(v_a_2184_) == 0)
{
lean_inc_ref(v_h_2084_);
v___y_2189_ = v_h_2084_;
goto v___jp_2188_;
}
else
{
lean_object* v_val_2196_; 
v_val_2196_ = lean_ctor_get(v_a_2184_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2184_, 1);
v___y_2189_ = v_val_2196_;
goto v___jp_2188_;
}
v___jp_2185_:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_mkAppB(v_g_2082_, v_a_2182_, v___y_2186_);
v_a_2095_ = v___x_2187_;
goto v___jp_2094_;
}
v___jp_2188_:
{
size_t v___x_2190_; size_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = lean_ptr_addr(v_prop_2083_);
lean_dec_ref(v_prop_2083_);
v___x_2191_ = lean_ptr_addr(v_a_2182_);
v___x_2192_ = lean_usize_dec_eq(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_dec_ref(v_h_2084_);
v___y_2186_ = v___y_2189_;
goto v___jp_2185_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_ptr_addr(v_h_2084_);
lean_dec_ref(v_h_2084_);
v___x_2194_ = lean_ptr_addr(v___y_2189_);
v___x_2195_ = lean_usize_dec_eq(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
v___y_2186_ = v___y_2189_;
goto v___jp_2185_;
}
else
{
lean_dec_ref(v___y_2189_);
lean_dec(v_a_2182_);
lean_dec_ref(v_g_2082_);
lean_inc_ref(v_e_2085_);
v_a_2095_ = v_e_2085_;
goto v___jp_2094_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2182_);
lean_dec_ref(v_e_2085_);
lean_dec_ref(v_h_2084_);
lean_dec_ref(v_prop_2083_);
lean_dec_ref(v_g_2082_);
v_a_2197_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2183_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2183_);
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
else
{
lean_dec_ref(v_h_2084_);
lean_dec_ref(v_prop_2083_);
lean_dec_ref(v_g_2082_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2181_, 1);
v_a_2095_ = v_a_2205_;
goto v___jp_2094_;
}
else
{
lean_dec_ref(v_e_2085_);
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v_canon_2207_; lean_object* v_cacheInType_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_g_2082_);
v___x_2206_ = lean_st_ref_get(v_a_2088_);
v_canon_2207_ = lean_ctor_get(v___x_2206_, 9);
lean_inc_ref(v_canon_2207_);
lean_dec(v___x_2206_);
v_cacheInType_2208_ = lean_ctor_get(v_canon_2207_, 1);
lean_inc_ref(v_cacheInType_2208_);
lean_dec_ref(v_canon_2207_);
v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2208_, v_e_2085_);
lean_dec_ref(v_cacheInType_2208_);
if (lean_obj_tag(v___x_2209_) == 1)
{
lean_object* v_val_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_e_2085_);
lean_dec_ref(v_h_2084_);
lean_dec_ref(v_prop_2083_);
v_val_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_val_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 0);
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_val_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v___x_2218_; 
lean_dec(v___x_2209_);
v___x_2218_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2083_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = 0;
v___x_2221_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2084_, v_a_2219_, v___x_2220_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
v___y_2129_ = v___x_2221_;
goto v___jp_2128_;
}
else
{
lean_dec_ref(v_h_2084_);
v___y_2129_ = v___x_2218_;
goto v___jp_2128_;
}
}
}
v___jp_2094_:
{
lean_object* v___x_2096_; lean_object* v_canon_2097_; lean_object* v_share_2098_; lean_object* v_maxFVar_2099_; lean_object* v_proofInstInfo_2100_; lean_object* v_inferType_2101_; lean_object* v_getLevel_2102_; lean_object* v_congrInfo_2103_; lean_object* v_defEqI_2104_; lean_object* v_extensions_2105_; lean_object* v_issues_2106_; lean_object* v_instanceOverrides_2107_; uint8_t v_debug_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2127_; 
v___x_2096_ = lean_st_ref_take(v_a_2088_);
v_canon_2097_ = lean_ctor_get(v___x_2096_, 9);
v_share_2098_ = lean_ctor_get(v___x_2096_, 0);
v_maxFVar_2099_ = lean_ctor_get(v___x_2096_, 1);
v_proofInstInfo_2100_ = lean_ctor_get(v___x_2096_, 2);
v_inferType_2101_ = lean_ctor_get(v___x_2096_, 3);
v_getLevel_2102_ = lean_ctor_get(v___x_2096_, 4);
v_congrInfo_2103_ = lean_ctor_get(v___x_2096_, 5);
v_defEqI_2104_ = lean_ctor_get(v___x_2096_, 6);
v_extensions_2105_ = lean_ctor_get(v___x_2096_, 7);
v_issues_2106_ = lean_ctor_get(v___x_2096_, 8);
v_instanceOverrides_2107_ = lean_ctor_get(v___x_2096_, 10);
v_debug_2108_ = lean_ctor_get_uint8(v___x_2096_, sizeof(void*)*11);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2110_ = v___x_2096_;
v_isShared_2111_ = v_isSharedCheck_2127_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_instanceOverrides_2107_);
lean_inc(v_canon_2097_);
lean_inc(v_issues_2106_);
lean_inc(v_extensions_2105_);
lean_inc(v_defEqI_2104_);
lean_inc(v_congrInfo_2103_);
lean_inc(v_getLevel_2102_);
lean_inc(v_inferType_2101_);
lean_inc(v_proofInstInfo_2100_);
lean_inc(v_maxFVar_2099_);
lean_inc(v_share_2098_);
lean_dec(v___x_2096_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2127_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_cache_2112_; lean_object* v_cacheInType_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2126_; 
v_cache_2112_ = lean_ctor_get(v_canon_2097_, 0);
v_cacheInType_2113_ = lean_ctor_get(v_canon_2097_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_canon_2097_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2115_ = v_canon_2097_;
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_cacheInType_2113_);
lean_inc(v_cache_2112_);
lean_dec(v_canon_2097_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_inc_ref(v_a_2095_);
v___x_2117_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2112_, v_e_2085_, v_a_2095_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_cacheInType_2113_);
v___x_2119_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 9, v___x_2119_);
v___x_2121_ = v___x_2110_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_share_2098_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_maxFVar_2099_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_proofInstInfo_2100_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_inferType_2101_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_getLevel_2102_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_congrInfo_2103_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_defEqI_2104_);
lean_ctor_set(v_reuseFailAlloc_2124_, 7, v_extensions_2105_);
lean_ctor_set(v_reuseFailAlloc_2124_, 8, v_issues_2106_);
lean_ctor_set(v_reuseFailAlloc_2124_, 9, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2124_, 10, v_instanceOverrides_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*11, v_debug_2108_);
v___x_2121_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_st_ref_put(v_a_2088_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2095_);
return v___x_2123_;
}
}
}
}
}
v___jp_2128_:
{
if (lean_obj_tag(v___y_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2168_; 
v_a_2130_ = lean_ctor_get(v___y_2129_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___y_2129_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2132_ = v___y_2129_;
v_isShared_2133_ = v_isSharedCheck_2168_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___y_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2168_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v_canon_2135_; lean_object* v_share_2136_; lean_object* v_maxFVar_2137_; lean_object* v_proofInstInfo_2138_; lean_object* v_inferType_2139_; lean_object* v_getLevel_2140_; lean_object* v_congrInfo_2141_; lean_object* v_defEqI_2142_; lean_object* v_extensions_2143_; lean_object* v_issues_2144_; lean_object* v_instanceOverrides_2145_; uint8_t v_debug_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2167_; 
v___x_2134_ = lean_st_ref_take(v_a_2088_);
v_canon_2135_ = lean_ctor_get(v___x_2134_, 9);
v_share_2136_ = lean_ctor_get(v___x_2134_, 0);
v_maxFVar_2137_ = lean_ctor_get(v___x_2134_, 1);
v_proofInstInfo_2138_ = lean_ctor_get(v___x_2134_, 2);
v_inferType_2139_ = lean_ctor_get(v___x_2134_, 3);
v_getLevel_2140_ = lean_ctor_get(v___x_2134_, 4);
v_congrInfo_2141_ = lean_ctor_get(v___x_2134_, 5);
v_defEqI_2142_ = lean_ctor_get(v___x_2134_, 6);
v_extensions_2143_ = lean_ctor_get(v___x_2134_, 7);
v_issues_2144_ = lean_ctor_get(v___x_2134_, 8);
v_instanceOverrides_2145_ = lean_ctor_get(v___x_2134_, 10);
v_debug_2146_ = lean_ctor_get_uint8(v___x_2134_, sizeof(void*)*11);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2148_ = v___x_2134_;
v_isShared_2149_ = v_isSharedCheck_2167_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_instanceOverrides_2145_);
lean_inc(v_canon_2135_);
lean_inc(v_issues_2144_);
lean_inc(v_extensions_2143_);
lean_inc(v_defEqI_2142_);
lean_inc(v_congrInfo_2141_);
lean_inc(v_getLevel_2140_);
lean_inc(v_inferType_2139_);
lean_inc(v_proofInstInfo_2138_);
lean_inc(v_maxFVar_2137_);
lean_inc(v_share_2136_);
lean_dec(v___x_2134_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2167_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_cache_2150_; lean_object* v_cacheInType_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2166_; 
v_cache_2150_ = lean_ctor_get(v_canon_2135_, 0);
v_cacheInType_2151_ = lean_ctor_get(v_canon_2135_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_canon_2135_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2153_ = v_canon_2135_;
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_cacheInType_2151_);
lean_inc(v_cache_2150_);
lean_dec(v_canon_2135_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_inc(v_a_2130_);
v___x_2155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2151_, v_e_2085_, v_a_2130_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2155_);
v___x_2157_ = v___x_2153_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_cache_2150_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 9, v___x_2157_);
v___x_2159_ = v___x_2148_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_share_2136_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_maxFVar_2137_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_proofInstInfo_2138_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_inferType_2139_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_getLevel_2140_);
lean_ctor_set(v_reuseFailAlloc_2164_, 5, v_congrInfo_2141_);
lean_ctor_set(v_reuseFailAlloc_2164_, 6, v_defEqI_2142_);
lean_ctor_set(v_reuseFailAlloc_2164_, 7, v_extensions_2143_);
lean_ctor_set(v_reuseFailAlloc_2164_, 8, v_issues_2144_);
lean_ctor_set(v_reuseFailAlloc_2164_, 9, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 10, v_instanceOverrides_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2164_, sizeof(void*)*11, v_debug_2146_);
v___x_2159_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_st_ref_put(v_a_2088_, v___x_2159_);
if (v_isShared_2133_ == 0)
{
v___x_2162_ = v___x_2132_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2130_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2085_);
return v___y_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2222_, lean_object* v_snd_2223_, lean_object* v_a_2224_, uint8_t v___x_2225_, lean_object* v_fst_2226_, lean_object* v___x_2227_, lean_object* v_____r_2228_, uint8_t v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_arg_x27_2238_; lean_object* v___x_2261_; 
lean_inc_ref(v___x_2222_);
v___x_2261_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2227_, v_a_2224_, v___x_2222_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; uint8_t v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = lean_unbox(v_a_2262_);
lean_dec(v_a_2262_);
switch(v___x_2263_)
{
case 0:
{
lean_object* v___x_2264_; 
lean_inc_ref(v___x_2222_);
v___x_2264_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2222_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_arg_x27_2238_ = v_a_2265_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
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
case 1:
{
lean_object* v___x_2274_; 
lean_inc_ref(v___x_2222_);
v___x_2274_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2222_, v___y_2233_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = l_Lean_Expr_cleanupAnnotations(v_a_2275_);
v___x_2277_ = l_Lean_Expr_isApp(v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v___x_2276_);
goto v___jp_2250_;
}
else
{
lean_object* v_arg_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_arg_2278_ = lean_ctor_get(v___x_2276_, 1);
lean_inc_ref(v_arg_2278_);
v___x_2279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2276_);
v___x_2280_ = l_Lean_Expr_isApp(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_dec_ref(v___x_2279_);
lean_dec_ref(v_arg_2278_);
goto v___jp_2250_;
}
else
{
lean_object* v_arg_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_arg_2281_ = lean_ctor_get(v___x_2279_, 1);
lean_inc_ref(v_arg_2281_);
v___x_2282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2279_);
v___x_2283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2284_ = l_Lean_Expr_isConstOf(v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2286_ = l_Lean_Expr_isConstOf(v___x_2282_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_dec_ref(v___x_2282_);
lean_dec_ref(v_arg_2281_);
lean_dec_ref(v_arg_2278_);
goto v___jp_2250_;
}
else
{
lean_object* v___x_2287_; 
lean_inc_ref(v___x_2222_);
v___x_2287_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2282_, v_arg_2281_, v_arg_2278_, v___x_2222_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_arg_x27_2238_ = v_a_2288_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2289_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
else
{
lean_object* v___x_2297_; 
lean_inc_ref(v___x_2222_);
v___x_2297_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2282_, v_arg_2281_, v_arg_2278_, v___x_2222_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v_arg_x27_2238_ = v_a_2298_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2299_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2297_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2297_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2307_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2274_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2274_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
default: 
{
lean_object* v___x_2315_; 
lean_inc_ref(v___x_2222_);
v___x_2315_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2222_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_arg_x27_2238_ = v_a_2316_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2317_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2315_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2315_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2325_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2261_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2261_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
v___jp_2237_:
{
size_t v___x_2239_; size_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2239_ = lean_ptr_addr(v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2240_ = lean_ptr_addr(v_arg_x27_2238_);
v___x_2241_ = lean_usize_dec_eq(v___x_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_fst_2226_);
v___x_2242_ = lean_array_fset(v_snd_2223_, v_a_2224_, v_arg_x27_2238_);
v___x_2243_ = lean_box(v___x_2225_);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v_arg_x27_2238_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_fst_2226_);
lean_ctor_set(v___x_2247_, 1, v_snd_2223_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
v___jp_2250_:
{
lean_object* v___x_2251_; 
lean_inc_ref(v___x_2222_);
v___x_2251_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2222_, v___x_2225_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_arg_x27_2238_ = v_a_2252_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_fst_2226_);
lean_dec(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v_a_2253_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
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
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2337_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2338_ = l_Lean_Name_append(v___x_2337_, v___x_2336_);
return v___x_2338_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2348_, lean_object* v___x_2349_, lean_object* v_a_2350_, lean_object* v_b_2351_, uint8_t v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___y_2361_; uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_lt(v_a_2350_, v_upperBound_2348_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_dec(v_a_2350_);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_b_2351_);
return v___x_2384_;
}
else
{
lean_object* v_toCold_2385_; lean_object* v_options_2386_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2452_; 
v_toCold_2385_ = lean_ctor_get(v___y_2357_, 0);
v_options_2386_ = lean_ctor_get(v_toCold_2385_, 2);
v_fst_2387_ = lean_ctor_get(v_b_2351_, 0);
v_snd_2388_ = lean_ctor_get(v_b_2351_, 1);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_b_2351_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2390_ = v_b_2351_;
v_isShared_2391_ = v_isSharedCheck_2452_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2388_);
lean_inc(v_fst_2387_);
lean_dec(v_b_2351_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2452_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_inheritedTraceOptions_2392_; uint8_t v_hasTrace_2393_; lean_object* v___x_2394_; 
v_inheritedTraceOptions_2392_ = lean_ctor_get(v_toCold_2385_, 11);
v_hasTrace_2393_ = lean_ctor_get_uint8(v_options_2386_, sizeof(void*)*1);
v___x_2394_ = lean_array_fget(v_snd_2388_, v_a_2350_);
if (v_hasTrace_2393_ == 0)
{
lean_del_object(v___x_2390_);
goto v___jp_2395_;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2399_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2400_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2392_, v_options_2386_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_del_object(v___x_2390_);
goto v___jp_2395_;
}
else
{
lean_object* v___x_2401_; 
lean_inc(v___x_2394_);
v___x_2401_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2349_, v_a_2350_, v___x_2394_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
lean_inc(v___y_2358_);
lean_inc_ref(v___y_2357_);
lean_inc(v___y_2356_);
lean_inc_ref(v___y_2355_);
lean_inc(v___x_2394_);
v___x_2403_ = lean_infer_type(v___x_2394_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v___y_2407_; uint8_t v___x_2431_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2431_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
switch(v___x_2431_)
{
case 0:
{
lean_object* v___x_2432_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2407_ = v___x_2432_;
goto v___jp_2406_;
}
case 1:
{
lean_object* v___x_2433_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2407_ = v___x_2433_;
goto v___jp_2406_;
}
case 2:
{
lean_object* v___x_2434_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2407_ = v___x_2434_;
goto v___jp_2406_;
}
default: 
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2407_ = v___x_2435_;
goto v___jp_2406_;
}
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
lean_inc(v___y_2407_);
v___x_2408_ = l_Lean_MessageData_ofFormat(v___y_2407_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 7);
lean_ctor_set(v___x_2390_, 1, v___x_2408_);
lean_ctor_set(v___x_2390_, 0, v___x_2405_);
v___x_2410_ = v___x_2390_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2411_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
lean_inc(v___x_2394_);
v___x_2413_ = l_Lean_MessageData_ofExpr(v___x_2394_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_MessageData_ofExpr(v_a_2404_);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2398_, v___x_2418_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2394_, v_snd_2388_, v_a_2350_, v___x_2383_, v_fst_2387_, v___x_2349_, v_a_2420_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
v___y_2361_ = v___x_2421_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v___x_2394_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
lean_dec(v_a_2350_);
v_a_2422_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2419_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2419_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2402_);
lean_dec(v___x_2394_);
lean_del_object(v___x_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
lean_dec(v_a_2350_);
v_a_2436_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2403_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2403_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___x_2394_);
lean_del_object(v___x_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
lean_dec(v_a_2350_);
v_a_2444_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2401_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2401_);
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
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
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
}
}
v___jp_2395_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_box(0);
v___x_2397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2394_, v_snd_2388_, v_a_2350_, v___x_2383_, v_fst_2387_, v___x_2349_, v___x_2396_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
v___y_2361_ = v___x_2397_;
goto v___jp_2360_;
}
}
}
v___jp_2360_:
{
if (lean_obj_tag(v___y_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2374_; 
v_a_2362_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2364_ = v___y_2361_;
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___y_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
if (lean_obj_tag(v_a_2362_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; 
lean_dec(v_a_2350_);
v_a_2366_ = lean_ctor_get(v_a_2362_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v_a_2362_, 1);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_a_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_del_object(v___x_2364_);
v_a_2370_ = lean_ctor_get(v_a_2362_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v_a_2362_, 1);
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_nat_add(v_a_2350_, v___x_2371_);
lean_dec(v_a_2350_);
v_a_2350_ = v___x_2372_;
v_b_2351_ = v_a_2370_;
goto _start;
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2350_);
v_a_2375_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___y_2361_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___y_2361_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_, uint8_t v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___y_2466_; uint8_t v_modified_2467_; lean_object* v_f_2468_; uint8_t v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v_args_2524_; uint8_t v_modified_2525_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; 
if (lean_obj_tag(v_x_2454_) == 5)
{
lean_object* v_fn_2561_; lean_object* v_arg_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_fn_2561_ = lean_ctor_get(v_x_2454_, 0);
lean_inc_ref(v_fn_2561_);
v_arg_2562_ = lean_ctor_get(v_x_2454_, 1);
lean_inc_ref(v_arg_2562_);
lean_dec_ref_known(v_x_2454_, 2);
v___x_2563_ = lean_array_set(v_x_2455_, v_x_2456_, v_arg_2562_);
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_nat_sub(v_x_2456_, v___x_2564_);
lean_dec(v_x_2456_);
v_x_2454_ = v_fn_2561_;
v_x_2455_ = v___x_2563_;
v_x_2456_ = v___x_2565_;
goto _start;
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
lean_dec(v_x_2456_);
v___x_2567_ = lean_array_get_size(v_x_2455_);
v___x_2568_ = lean_unsigned_to_nat(2u);
v___x_2569_ = lean_nat_dec_eq(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2540_ = v___y_2457_;
v___y_2541_ = v___y_2458_;
v___y_2542_ = v___y_2459_;
v___y_2543_ = v___y_2460_;
v___y_2544_ = v___y_2461_;
v___y_2545_ = v___y_2462_;
v___y_2546_ = v___y_2463_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = l_Lean_instInhabitedExpr;
v___x_2571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2572_ = l_Lean_Expr_isConstOf(v_x_2454_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2574_ = l_Lean_Expr_isConstOf(v_x_2454_, v___x_2573_);
if (v___x_2574_ == 0)
{
v___y_2540_ = v___y_2457_;
v___y_2541_ = v___y_2458_;
v___y_2542_ = v___y_2459_;
v___y_2543_ = v___y_2460_;
v___y_2544_ = v___y_2461_;
v___y_2545_ = v___y_2462_;
v___y_2546_ = v___y_2463_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_array_get(v___x_2570_, v_x_2455_, v___x_2575_);
v___x_2577_ = lean_unsigned_to_nat(1u);
v___x_2578_ = lean_array_get(v___x_2570_, v_x_2455_, v___x_2577_);
lean_dec_ref(v_x_2455_);
v___x_2579_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2454_, v___x_2576_, v___x_2578_, v_e_2453_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2579_;
}
}
else
{
lean_object* v___x_2580_; lean_object* v_prop_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(0u);
v_prop_2581_ = lean_array_get_borrowed(v___x_2570_, v_x_2455_, v___x_2580_);
lean_inc(v_prop_2581_);
v___x_2582_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2581_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2599_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2599_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2599_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
size_t v___x_2587_; size_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_ptr_addr(v_prop_2581_);
v___x_2588_ = lean_ptr_addr(v_a_2583_);
v___x_2589_ = lean_usize_dec_eq(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_dec_ref(v_e_2453_);
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_array_get(v___x_2570_, v_x_2455_, v___x_2590_);
lean_dec_ref(v_x_2455_);
v___x_2592_ = l_Lean_mkAppB(v_x_2454_, v_a_2583_, v___x_2591_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2592_);
v___x_2594_ = v___x_2585_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2597_; 
lean_dec(v_a_2583_);
lean_dec_ref(v_x_2455_);
lean_dec_ref(v_x_2454_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_e_2453_);
v___x_2597_ = v___x_2585_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_e_2453_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_dec_ref(v_x_2455_);
lean_dec_ref(v_x_2454_);
lean_dec_ref(v_e_2453_);
return v___x_2582_;
}
}
}
}
v___jp_2465_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
lean_inc_ref(v_f_2468_);
v___x_2477_ = l_Lean_Meta_getFunInfo(v_f_2468_, v___x_2476_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_paramInfo_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2513_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v_paramInfo_2479_ = lean_ctor_get(v_a_2478_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v_a_2478_, 1);
lean_dec(v_unused_2514_);
v___x_2481_ = v_a_2478_;
v_isShared_2482_ = v_isSharedCheck_2513_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_paramInfo_2479_);
lean_dec(v_a_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2513_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2483_ = lean_array_get_size(v___y_2466_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_box(v_modified_2467_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___y_2466_);
lean_ctor_set(v___x_2481_, 0, v___x_2485_);
v___x_2487_ = v___x_2481_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___y_2466_);
v___x_2487_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2483_, v_paramInfo_2479_, v___x_2484_, v___x_2487_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec_ref(v_paramInfo_2479_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2503_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2503_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2503_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_fst_2493_; uint8_t v___x_2494_; 
v_fst_2493_ = lean_ctor_get(v_a_2489_, 0);
v___x_2494_ = lean_unbox(v_fst_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2496_; 
lean_dec(v_a_2489_);
lean_dec_ref(v_f_2468_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_e_2453_);
v___x_2496_ = v___x_2491_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_e_2453_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
else
{
lean_object* v_snd_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_dec_ref(v_e_2453_);
v_snd_2498_ = lean_ctor_get(v_a_2489_, 1);
lean_inc(v_snd_2498_);
lean_dec(v_a_2489_);
v___x_2499_ = l_Lean_mkAppN(v_f_2468_, v_snd_2498_);
lean_dec(v_snd_2498_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2499_);
v___x_2501_ = v___x_2491_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v_f_2468_);
lean_dec_ref(v_e_2453_);
v_a_2504_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2488_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2488_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v_f_2468_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v_e_2453_);
v_a_2515_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2477_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2477_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
v___jp_2523_:
{
lean_object* v___x_2533_; 
lean_inc_ref(v_x_2454_);
v___x_2533_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2454_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; size_t v___x_2535_; size_t v___x_2536_; uint8_t v___x_2537_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = lean_ptr_addr(v_x_2454_);
v___x_2536_ = lean_ptr_addr(v_a_2534_);
v___x_2537_ = lean_usize_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
uint8_t v___x_2538_; 
lean_dec_ref(v_x_2454_);
v___x_2538_ = 1;
v___y_2466_ = v_args_2524_;
v_modified_2467_ = v___x_2538_;
v_f_2468_ = v_a_2534_;
v___y_2469_ = v___y_2526_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___y_2531_;
v___y_2475_ = v___y_2532_;
goto v___jp_2465_;
}
else
{
lean_dec(v_a_2534_);
v___y_2466_ = v_args_2524_;
v_modified_2467_ = v_modified_2525_;
v_f_2468_ = v_x_2454_;
v___y_2469_ = v___y_2526_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___y_2531_;
v___y_2475_ = v___y_2532_;
goto v___jp_2465_;
}
}
else
{
lean_dec_ref(v_args_2524_);
lean_dec_ref(v_x_2454_);
lean_dec_ref(v_e_2453_);
return v___x_2533_;
}
}
v___jp_2539_:
{
uint8_t v_modified_2547_; lean_object* v___x_2548_; uint8_t v_modified_2549_; 
v_modified_2547_ = 0;
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2549_ = l_Lean_Expr_isConstOf(v_x_2454_, v___x_2548_);
if (v_modified_2549_ == 0)
{
v_args_2524_ = v_x_2455_;
v_modified_2525_ = v_modified_2547_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2545_;
v___y_2532_ = v___y_2546_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2550_; 
lean_inc_ref(v_x_2455_);
v___x_2550_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2455_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
if (lean_obj_tag(v_a_2551_) == 1)
{
lean_object* v_val_2552_; 
lean_dec_ref(v_x_2455_);
v_val_2552_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_a_2551_, 1);
v_args_2524_ = v_val_2552_;
v_modified_2525_ = v_modified_2549_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2545_;
v___y_2532_ = v___y_2546_;
goto v___jp_2523_;
}
else
{
lean_dec(v_a_2551_);
v_args_2524_ = v_x_2455_;
v_modified_2525_ = v_modified_2547_;
v___y_2526_ = v___y_2540_;
v___y_2527_ = v___y_2541_;
v___y_2528_ = v___y_2542_;
v___y_2529_ = v___y_2543_;
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2545_;
v___y_2532_ = v___y_2546_;
goto v___jp_2523_;
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_x_2455_);
lean_dec_ref(v_x_2454_);
lean_dec_ref(v_e_2453_);
v_a_2553_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2550_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2550_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2600_, uint8_t v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_dummy_2609_; lean_object* v_nargs_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_dummy_2609_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2610_ = l_Lean_Expr_getAppNumArgs(v_e_2600_);
lean_inc(v_nargs_2610_);
v___x_2611_ = lean_mk_array(v_nargs_2610_, v_dummy_2609_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v_nargs_2610_, v___x_2612_);
lean_dec(v_nargs_2610_);
lean_inc_ref(v_e_2600_);
v___x_2614_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2600_, v_e_2600_, v___x_2611_, v___x_2613_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2615_, uint8_t v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
uint8_t v___x_2644_; 
lean_inc_ref(v_e_2615_);
v___x_2644_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2615_);
if (v___x_2644_ == 0)
{
lean_object* v_f_2645_; 
v_f_2645_ = l_Lean_Expr_getAppFn(v_e_2615_);
if (lean_obj_tag(v_f_2645_) == 4)
{
lean_object* v_declName_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_declName_2646_ = lean_ctor_get(v_f_2645_, 0);
lean_inc(v_declName_2646_);
lean_dec_ref_known(v_f_2645_, 2);
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0));
v___x_2648_ = lean_name_eq(v_declName_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2650_ = lean_name_eq(v_declName_2646_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2652_ = lean_name_eq(v_declName_2646_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2654_ = lean_name_eq(v_declName_2646_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2646_, v_a_2622_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2685_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2685_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2685_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
if (lean_obj_tag(v_a_2656_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
lean_del_object(v___x_2658_);
v_val_2660_ = lean_ctor_get(v_a_2656_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v_a_2656_, 1);
lean_inc_ref(v_e_2615_);
v___x_2661_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2660_, v_e_2615_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_val_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2673_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_a_2662_) == 0)
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v_e_2615_);
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_e_2615_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2671_; 
lean_dec_ref(v_e_2615_);
v_val_2669_ = lean_ctor_get(v_a_2662_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_a_2662_, 1);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v_val_2669_);
v___x_2671_ = v___x_2664_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_val_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v_e_2615_);
v_a_2674_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2661_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2661_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_e_2615_);
v___x_2683_ = v___x_2658_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_e_2615_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_e_2615_);
v_a_2686_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2655_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2655_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_dec(v_declName_2646_);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_declName_2646_);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_declName_2646_);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_declName_2646_);
goto v___jp_2624_;
}
}
else
{
lean_object* v___x_2694_; 
lean_dec_ref(v_f_2645_);
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_e_2615_);
return v___x_2694_;
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_inc_ref(v_e_2615_);
v___x_2695_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2695_, 0, v_e_2615_);
v___x_2696_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2695_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2730_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2730_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2730_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
if (lean_obj_tag(v_a_2697_) == 1)
{
lean_object* v_val_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_dec_ref(v_e_2615_);
v_val_2701_ = lean_ctor_get(v_a_2697_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v_a_2697_, 1);
v___x_2702_ = l_Lean_mkNatLit(v_val_2701_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2702_);
v___x_2704_ = v___x_2699_;
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
else
{
lean_object* v___x_2706_; 
lean_del_object(v___x_2699_);
lean_dec(v_a_2697_);
lean_inc_ref(v_e_2615_);
v___x_2706_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2615_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2721_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2721_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2721_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
if (lean_obj_tag(v_a_2707_) == 1)
{
lean_object* v_val_2711_; lean_object* v_fst_2712_; lean_object* v_snd_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_dec_ref(v_e_2615_);
v_val_2711_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v_a_2707_, 1);
v_fst_2712_ = lean_ctor_get(v_val_2711_, 0);
lean_inc(v_fst_2712_);
v_snd_2713_ = lean_ctor_get(v_val_2711_, 1);
lean_inc(v_snd_2713_);
lean_dec(v_val_2711_);
v___x_2714_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2712_, v_snd_2713_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2714_);
v___x_2716_ = v___x_2709_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
else
{
lean_object* v___x_2719_; 
lean_dec(v_a_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v_e_2615_);
v___x_2719_ = v___x_2709_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_e_2615_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v_e_2615_);
v_a_2722_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2706_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2706_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v_e_2615_);
v_a_2731_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2696_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2696_);
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
v___jp_2624_:
{
lean_object* v___x_2625_; 
lean_inc_ref(v_e_2615_);
v___x_2625_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2615_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2635_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
if (lean_obj_tag(v_a_2626_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2631_; 
lean_del_object(v___x_2628_);
lean_dec_ref(v_e_2615_);
v_val_2630_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v_a_2626_, 1);
v___x_2631_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2630_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
return v___x_2631_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_a_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_e_2615_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_e_2615_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v_e_2615_);
v_a_2636_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2625_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2625_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2739_, uint8_t v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2749_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
return v___x_2750_;
}
else
{
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2751_, uint8_t v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2751_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
if (lean_obj_tag(v_a_2761_) == 0)
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v_e_2751_);
v_val_2762_ = lean_ctor_get(v_a_2761_, 0);
lean_inc_ref(v_val_2762_);
lean_dec_ref_known(v_a_2761_, 1);
v___x_2763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2762_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
return v___x_2763_;
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_a_2761_);
v___x_2764_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2765_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2776_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2776_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2776_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
if (lean_obj_tag(v_a_2767_) == 0)
{
lean_object* v_val_2771_; lean_object* v___x_2772_; 
lean_del_object(v___x_2769_);
lean_dec(v_a_2765_);
v_val_2771_ = lean_ctor_get(v_a_2767_, 0);
lean_inc_ref(v_val_2771_);
lean_dec_ref_known(v_a_2767_, 1);
v___x_2772_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2771_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
return v___x_2772_;
}
else
{
lean_object* v___x_2774_; 
lean_dec(v_a_2767_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v_a_2765_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2765_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2765_);
v_a_2777_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2766_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2766_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_e_2751_);
v_a_2785_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2760_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2760_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2799_, uint8_t v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
uint8_t v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___x_2818_; 
lean_inc_ref(v_e_2799_);
v___x_2818_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2799_, v_a_2804_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l_Lean_Expr_cleanupAnnotations(v_a_2819_);
v___x_2821_ = l_Lean_Expr_isApp(v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec_ref(v___x_2820_);
v___y_2809_ = v_a_2800_;
v___y_2810_ = v_a_2801_;
v___y_2811_ = v_a_2802_;
v___y_2812_ = v_a_2803_;
v___y_2813_ = v_a_2804_;
v___y_2814_ = v_a_2805_;
v___y_2815_ = v_a_2806_;
goto v___jp_2808_;
}
else
{
lean_object* v_arg_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_arg_2822_ = lean_ctor_get(v___x_2820_, 1);
lean_inc_ref(v_arg_2822_);
v___x_2823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2820_);
v___x_2824_ = l_Lean_Expr_isApp(v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec_ref(v___x_2823_);
lean_dec_ref(v_arg_2822_);
v___y_2809_ = v_a_2800_;
v___y_2810_ = v_a_2801_;
v___y_2811_ = v_a_2802_;
v___y_2812_ = v_a_2803_;
v___y_2813_ = v_a_2804_;
v___y_2814_ = v_a_2805_;
v___y_2815_ = v_a_2806_;
goto v___jp_2808_;
}
else
{
lean_object* v_arg_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_arg_2825_ = lean_ctor_get(v___x_2823_, 1);
lean_inc_ref(v_arg_2825_);
v___x_2826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2823_);
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2828_ = l_Lean_Expr_isConstOf(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_dec_ref(v___x_2826_);
lean_dec_ref(v_arg_2825_);
lean_dec_ref(v_arg_2822_);
v___y_2809_ = v_a_2800_;
v___y_2810_ = v_a_2801_;
v___y_2811_ = v_a_2802_;
v___y_2812_ = v_a_2803_;
v___y_2813_ = v_a_2804_;
v___y_2814_ = v_a_2805_;
v___y_2815_ = v_a_2806_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2826_, v_arg_2825_, v_arg_2822_, v_e_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
return v___x_2829_;
}
}
}
}
else
{
lean_dec_ref(v_e_2799_);
return v___x_2818_;
}
v___jp_2808_:
{
uint8_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = 0;
v___x_2817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2799_, v___x_2816_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2830_, lean_object* v_00_u03b1_2831_, lean_object* v_c_2832_, lean_object* v_inst_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_, uint8_t v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2832_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; uint8_t v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_n(v_a_2845_, 2);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2845_);
if (v___x_2846_ == 0)
{
uint8_t v___x_2847_; 
lean_inc(v_a_2845_);
v___x_2847_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2845_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2831_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2833_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2834_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2863_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2863_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2863_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2859_ = l_Lean_mkApp5(v_f_2830_, v_a_2849_, v_a_2845_, v_a_2851_, v_a_2853_, v_a_2855_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2859_);
v___x_2861_ = v___x_2857_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
else
{
lean_dec(v_a_2853_);
lean_dec(v_a_2851_);
lean_dec(v_a_2849_);
lean_dec(v_a_2845_);
lean_dec_ref(v_f_2830_);
return v___x_2854_;
}
}
else
{
lean_dec(v_a_2851_);
lean_dec(v_a_2849_);
lean_dec(v_a_2845_);
lean_dec_ref(v_b_2835_);
lean_dec_ref(v_f_2830_);
return v___x_2852_;
}
}
else
{
lean_dec(v_a_2849_);
lean_dec(v_a_2845_);
lean_dec_ref(v_b_2835_);
lean_dec_ref(v_a_2834_);
lean_dec_ref(v_f_2830_);
return v___x_2850_;
}
}
else
{
lean_dec(v_a_2845_);
lean_dec_ref(v_b_2835_);
lean_dec_ref(v_a_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_f_2830_);
return v___x_2848_;
}
}
else
{
lean_object* v___x_2864_; 
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_00_u03b1_2831_);
lean_dec_ref(v_f_2830_);
v___x_2864_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2864_;
}
}
else
{
lean_object* v___x_2865_; 
lean_dec(v_a_2845_);
lean_dec_ref(v_b_2835_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_00_u03b1_2831_);
lean_dec_ref(v_f_2830_);
v___x_2865_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2834_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2865_;
}
}
else
{
lean_dec_ref(v_b_2835_);
lean_dec_ref(v_a_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_00_u03b1_2831_);
lean_dec_ref(v_f_2830_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2866_, lean_object* v_00_u03b1_2867_, lean_object* v_c_2868_, lean_object* v_a_2869_, lean_object* v_b_2870_, uint8_t v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2868_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; uint8_t v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc_n(v_a_2880_, 2);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = l_Lean_Expr_isBoolTrue(v_a_2880_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
lean_inc(v_a_2880_);
v___x_2882_ = l_Lean_Expr_isBoolFalse(v_a_2880_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2867_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2869_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2896_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = l_Lean_mkApp4(v_f_2866_, v_a_2884_, v_a_2880_, v_a_2886_, v_a_2888_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2892_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_dec(v_a_2886_);
lean_dec(v_a_2884_);
lean_dec(v_a_2880_);
lean_dec_ref(v_f_2866_);
return v___x_2887_;
}
}
else
{
lean_dec(v_a_2884_);
lean_dec(v_a_2880_);
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_f_2866_);
return v___x_2885_;
}
}
else
{
lean_dec(v_a_2880_);
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_f_2866_);
return v___x_2883_;
}
}
else
{
lean_object* v___x_2897_; 
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_f_2866_);
v___x_2897_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2897_;
}
}
else
{
lean_object* v___x_2898_; 
lean_dec(v_a_2880_);
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_f_2866_);
v___x_2898_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2869_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2898_;
}
}
else
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_f_2866_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2899_, uint8_t v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; uint8_t v___y_2916_; uint8_t v___y_2917_; uint8_t v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___x_2945_; 
lean_inc_ref(v_e_2899_);
v___x_2945_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2899_, v_a_2904_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = l_Lean_Expr_cleanupAnnotations(v_a_2946_);
v___x_2948_ = l_Lean_Expr_isApp(v___x_2947_);
if (v___x_2948_ == 0)
{
lean_dec_ref(v___x_2947_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v_arg_2949_ = lean_ctor_get(v___x_2947_, 1);
lean_inc_ref(v_arg_2949_);
v___x_2950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2947_);
v___x_2951_ = l_Lean_Expr_isApp(v___x_2950_);
if (v___x_2951_ == 0)
{
lean_dec_ref(v___x_2950_);
lean_dec_ref(v_arg_2949_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_arg_2952_ = lean_ctor_get(v___x_2950_, 1);
lean_inc_ref(v_arg_2952_);
v___x_2953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2950_);
v___x_2954_ = l_Lean_Expr_isApp(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_arg_2952_);
lean_dec_ref(v_arg_2949_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_arg_2955_ = lean_ctor_get(v___x_2953_, 1);
lean_inc_ref(v_arg_2955_);
v___x_2956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2953_);
v___x_2957_ = l_Lean_Expr_isApp(v___x_2956_);
if (v___x_2957_ == 0)
{
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_arg_2955_);
lean_dec_ref(v_arg_2952_);
lean_dec_ref(v_arg_2949_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_arg_2958_ = lean_ctor_get(v___x_2956_, 1);
lean_inc_ref(v_arg_2958_);
v___x_2959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2956_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2961_ = l_Lean_Expr_isConstOf(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
uint8_t v___x_2962_; 
v___x_2962_ = l_Lean_Expr_isApp(v___x_2959_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_arg_2958_);
lean_dec_ref(v_arg_2955_);
lean_dec_ref(v_arg_2952_);
lean_dec_ref(v_arg_2949_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v_arg_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_arg_2963_ = lean_ctor_get(v___x_2959_, 1);
lean_inc_ref(v_arg_2963_);
v___x_2964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2959_);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2966_ = l_Lean_Expr_isConstOf(v___x_2964_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v___x_2964_);
lean_dec_ref(v_arg_2963_);
lean_dec_ref(v_arg_2958_);
lean_dec_ref(v_arg_2955_);
lean_dec_ref(v_arg_2952_);
lean_dec_ref(v_arg_2949_);
v___y_2936_ = v_a_2900_;
v___y_2937_ = v_a_2901_;
v___y_2938_ = v_a_2902_;
v___y_2939_ = v_a_2903_;
v___y_2940_ = v_a_2904_;
v___y_2941_ = v_a_2905_;
v___y_2942_ = v_a_2906_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2967_; 
lean_dec_ref(v_e_2899_);
v___x_2967_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2964_, v_arg_2963_, v_arg_2958_, v_arg_2955_, v_arg_2952_, v_arg_2949_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
return v___x_2967_;
}
}
}
else
{
lean_object* v___x_2968_; 
lean_dec_ref(v_e_2899_);
v___x_2968_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2959_, v_arg_2958_, v_arg_2955_, v_arg_2952_, v_arg_2949_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
return v___x_2968_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2899_);
return v___x_2945_;
}
v___jp_2908_:
{
if (v___y_2917_ == 0)
{
if (lean_obj_tag(v___y_2910_) == 4)
{
lean_object* v_declName_2918_; lean_object* v___x_2919_; 
v_declName_2918_ = lean_ctor_get(v___y_2910_, 0);
lean_inc(v_declName_2918_);
lean_dec_ref_known(v___y_2910_, 2);
v___x_2919_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2918_, v___y_2911_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; uint8_t v___x_2921_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_unbox(v_a_2920_);
lean_dec(v_a_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2899_, v___y_2916_, v___y_2909_, v___y_2913_, v___y_2912_, v___y_2914_, v___y_2915_, v___y_2911_);
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; 
v___x_2923_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2899_, v___y_2916_, v___y_2909_, v___y_2913_, v___y_2912_, v___y_2914_, v___y_2915_, v___y_2911_);
return v___x_2923_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_e_2899_);
v_a_2924_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2919_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2919_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v___x_2932_; 
lean_dec_ref(v___y_2910_);
v___x_2932_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2899_, v___y_2916_, v___y_2909_, v___y_2913_, v___y_2912_, v___y_2914_, v___y_2915_, v___y_2911_);
return v___x_2932_;
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec_ref(v___y_2910_);
v___x_2933_ = l_Lean_Expr_headBeta(v_e_2899_);
v___x_2934_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2933_, v___y_2916_, v___y_2909_, v___y_2913_, v___y_2912_, v___y_2914_, v___y_2915_, v___y_2911_);
return v___x_2934_;
}
}
v___jp_2935_:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = l_Lean_Expr_getAppFn(v_e_2899_);
v___x_2944_ = l_Lean_Expr_isLambda(v___x_2943_);
if (v___x_2944_ == 0)
{
v___y_2909_ = v___y_2937_;
v___y_2910_ = v___x_2943_;
v___y_2911_ = v___y_2942_;
v___y_2912_ = v___y_2939_;
v___y_2913_ = v___y_2938_;
v___y_2914_ = v___y_2940_;
v___y_2915_ = v___y_2941_;
v___y_2916_ = v___y_2936_;
v___y_2917_ = v___x_2944_;
goto v___jp_2908_;
}
else
{
v___y_2909_ = v___y_2937_;
v___y_2910_ = v___x_2943_;
v___y_2911_ = v___y_2942_;
v___y_2912_ = v___y_2939_;
v___y_2913_ = v___y_2938_;
v___y_2914_ = v___y_2940_;
v___y_2915_ = v___y_2941_;
v___y_2916_ = v___y_2936_;
v___y_2917_ = v___y_2936_;
goto v___jp_2908_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2973_ = lean_unsigned_to_nat(18u);
v___x_2974_ = lean_unsigned_to_nat(1895u);
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2977_ = l_mkPanicMessageWithDecl(v___x_2976_, v___x_2975_, v___x_2974_, v___x_2973_, v___x_2972_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2978_, uint8_t v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_Expr_projExpr_x21(v_e_2978_);
v___x_2988_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2987_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___y_2991_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
if (lean_obj_tag(v_e_2978_) == 11)
{
lean_object* v_typeName_3013_; lean_object* v_idx_3014_; lean_object* v_struct_3015_; size_t v___x_3016_; size_t v___x_3017_; uint8_t v___x_3018_; 
v_typeName_3013_ = lean_ctor_get(v_e_2978_, 0);
v_idx_3014_ = lean_ctor_get(v_e_2978_, 1);
v_struct_3015_ = lean_ctor_get(v_e_2978_, 2);
v___x_3016_ = lean_ptr_addr(v_struct_3015_);
v___x_3017_ = lean_ptr_addr(v_a_2989_);
v___x_3018_ = lean_usize_dec_eq(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; 
lean_inc(v_idx_3014_);
lean_inc(v_typeName_3013_);
lean_dec_ref_known(v_e_2978_, 3);
v___x_3019_ = l_Lean_Expr_proj___override(v_typeName_3013_, v_idx_3014_, v_a_2989_);
v___y_2991_ = v___x_3019_;
goto v___jp_2990_;
}
else
{
lean_dec(v_a_2989_);
v___y_2991_ = v_e_2978_;
goto v___jp_2990_;
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec(v_a_2989_);
lean_dec_ref(v_e_2978_);
v___x_3020_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3021_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3020_);
v___y_2991_ = v___x_3021_;
goto v___jp_2990_;
}
v___jp_2990_:
{
lean_object* v___x_2992_; 
lean_inc_ref(v___y_2991_);
v___x_2992_ = l_Lean_Meta_reduceProj_x3f(v___y_2991_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3004_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
if (lean_obj_tag(v_a_2993_) == 0)
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___y_2991_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___y_2991_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v_val_3000_; lean_object* v___x_3002_; 
lean_dec_ref(v___y_2991_);
v_val_3000_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_val_3000_);
lean_dec_ref_known(v_a_2993_, 1);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_val_3000_);
v___x_3002_ = v___x_2995_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_val_3000_);
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
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v___y_2991_);
v_a_3005_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2992_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2992_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2978_);
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3022_, uint8_t v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
switch(lean_obj_tag(v_e_3022_))
{
case 7:
{
lean_object* v___x_3031_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3023_ == 0)
{
lean_object* v___x_3032_; lean_object* v_canon_3033_; lean_object* v_cache_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_st_ref_get(v_a_3025_);
v_canon_3033_ = lean_ctor_get(v___x_3032_, 9);
lean_inc_ref(v_canon_3033_);
lean_dec(v___x_3032_);
v_cache_3034_ = lean_ctor_get(v_canon_3033_, 0);
lean_inc_ref(v_cache_3034_);
lean_dec_ref(v_canon_3033_);
v___x_3035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3034_, v_e_3022_);
lean_dec_ref(v_cache_3034_);
if (lean_obj_tag(v___x_3035_) == 1)
{
lean_object* v_val_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_val_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 0);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_val_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_object* v___x_3044_; 
lean_dec(v___x_3035_);
lean_inc_ref(v_e_3022_);
v___x_3044_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3031_, v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3083_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3083_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3083_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v_canon_3050_; lean_object* v_share_3051_; lean_object* v_maxFVar_3052_; lean_object* v_proofInstInfo_3053_; lean_object* v_inferType_3054_; lean_object* v_getLevel_3055_; lean_object* v_congrInfo_3056_; lean_object* v_defEqI_3057_; lean_object* v_extensions_3058_; lean_object* v_issues_3059_; lean_object* v_instanceOverrides_3060_; uint8_t v_debug_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3082_; 
v___x_3049_ = lean_st_ref_take(v_a_3025_);
v_canon_3050_ = lean_ctor_get(v___x_3049_, 9);
v_share_3051_ = lean_ctor_get(v___x_3049_, 0);
v_maxFVar_3052_ = lean_ctor_get(v___x_3049_, 1);
v_proofInstInfo_3053_ = lean_ctor_get(v___x_3049_, 2);
v_inferType_3054_ = lean_ctor_get(v___x_3049_, 3);
v_getLevel_3055_ = lean_ctor_get(v___x_3049_, 4);
v_congrInfo_3056_ = lean_ctor_get(v___x_3049_, 5);
v_defEqI_3057_ = lean_ctor_get(v___x_3049_, 6);
v_extensions_3058_ = lean_ctor_get(v___x_3049_, 7);
v_issues_3059_ = lean_ctor_get(v___x_3049_, 8);
v_instanceOverrides_3060_ = lean_ctor_get(v___x_3049_, 10);
v_debug_3061_ = lean_ctor_get_uint8(v___x_3049_, sizeof(void*)*11);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3063_ = v___x_3049_;
v_isShared_3064_ = v_isSharedCheck_3082_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_instanceOverrides_3060_);
lean_inc(v_canon_3050_);
lean_inc(v_issues_3059_);
lean_inc(v_extensions_3058_);
lean_inc(v_defEqI_3057_);
lean_inc(v_congrInfo_3056_);
lean_inc(v_getLevel_3055_);
lean_inc(v_inferType_3054_);
lean_inc(v_proofInstInfo_3053_);
lean_inc(v_maxFVar_3052_);
lean_inc(v_share_3051_);
lean_dec(v___x_3049_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3082_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v_cache_3065_; lean_object* v_cacheInType_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3081_; 
v_cache_3065_ = lean_ctor_get(v_canon_3050_, 0);
v_cacheInType_3066_ = lean_ctor_get(v_canon_3050_, 1);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_canon_3050_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3068_ = v_canon_3050_;
v_isShared_3069_ = v_isSharedCheck_3081_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_cacheInType_3066_);
lean_inc(v_cache_3065_);
lean_dec(v_canon_3050_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3081_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
lean_inc(v_a_3045_);
v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3065_, v_e_3022_, v_a_3045_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3070_);
v___x_3072_ = v___x_3068_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_cacheInType_3066_);
v___x_3072_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 9, v___x_3072_);
v___x_3074_ = v___x_3063_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_share_3051_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_maxFVar_3052_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_proofInstInfo_3053_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_inferType_3054_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_getLevel_3055_);
lean_ctor_set(v_reuseFailAlloc_3079_, 5, v_congrInfo_3056_);
lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_defEqI_3057_);
lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_extensions_3058_);
lean_ctor_set(v_reuseFailAlloc_3079_, 8, v_issues_3059_);
lean_ctor_set(v_reuseFailAlloc_3079_, 9, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3079_, 10, v_instanceOverrides_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3079_, sizeof(void*)*11, v_debug_3061_);
v___x_3074_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3075_ = lean_st_ref_put(v_a_3025_, v___x_3074_);
if (v_isShared_3048_ == 0)
{
v___x_3077_ = v___x_3047_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3045_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3044_;
}
}
}
else
{
lean_object* v___x_3084_; lean_object* v_canon_3085_; lean_object* v_cacheInType_3086_; lean_object* v___x_3087_; 
v___x_3084_ = lean_st_ref_get(v_a_3025_);
v_canon_3085_ = lean_ctor_get(v___x_3084_, 9);
lean_inc_ref(v_canon_3085_);
lean_dec(v___x_3084_);
v_cacheInType_3086_ = lean_ctor_get(v_canon_3085_, 1);
lean_inc_ref(v_cacheInType_3086_);
lean_dec_ref(v_canon_3085_);
v___x_3087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3086_, v_e_3022_);
lean_dec_ref(v_cacheInType_3086_);
if (lean_obj_tag(v___x_3087_) == 1)
{
lean_object* v_val_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_val_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set_tag(v___x_3090_, 0);
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_val_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_object* v___x_3096_; 
lean_dec(v___x_3087_);
lean_inc_ref(v_e_3022_);
v___x_3096_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3031_, v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3135_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v_canon_3102_; lean_object* v_share_3103_; lean_object* v_maxFVar_3104_; lean_object* v_proofInstInfo_3105_; lean_object* v_inferType_3106_; lean_object* v_getLevel_3107_; lean_object* v_congrInfo_3108_; lean_object* v_defEqI_3109_; lean_object* v_extensions_3110_; lean_object* v_issues_3111_; lean_object* v_instanceOverrides_3112_; uint8_t v_debug_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3134_; 
v___x_3101_ = lean_st_ref_take(v_a_3025_);
v_canon_3102_ = lean_ctor_get(v___x_3101_, 9);
v_share_3103_ = lean_ctor_get(v___x_3101_, 0);
v_maxFVar_3104_ = lean_ctor_get(v___x_3101_, 1);
v_proofInstInfo_3105_ = lean_ctor_get(v___x_3101_, 2);
v_inferType_3106_ = lean_ctor_get(v___x_3101_, 3);
v_getLevel_3107_ = lean_ctor_get(v___x_3101_, 4);
v_congrInfo_3108_ = lean_ctor_get(v___x_3101_, 5);
v_defEqI_3109_ = lean_ctor_get(v___x_3101_, 6);
v_extensions_3110_ = lean_ctor_get(v___x_3101_, 7);
v_issues_3111_ = lean_ctor_get(v___x_3101_, 8);
v_instanceOverrides_3112_ = lean_ctor_get(v___x_3101_, 10);
v_debug_3113_ = lean_ctor_get_uint8(v___x_3101_, sizeof(void*)*11);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3115_ = v___x_3101_;
v_isShared_3116_ = v_isSharedCheck_3134_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_instanceOverrides_3112_);
lean_inc(v_canon_3102_);
lean_inc(v_issues_3111_);
lean_inc(v_extensions_3110_);
lean_inc(v_defEqI_3109_);
lean_inc(v_congrInfo_3108_);
lean_inc(v_getLevel_3107_);
lean_inc(v_inferType_3106_);
lean_inc(v_proofInstInfo_3105_);
lean_inc(v_maxFVar_3104_);
lean_inc(v_share_3103_);
lean_dec(v___x_3101_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3134_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v_cache_3117_; lean_object* v_cacheInType_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3133_; 
v_cache_3117_ = lean_ctor_get(v_canon_3102_, 0);
v_cacheInType_3118_ = lean_ctor_get(v_canon_3102_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_canon_3102_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3120_ = v_canon_3102_;
v_isShared_3121_ = v_isSharedCheck_3133_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_cacheInType_3118_);
lean_inc(v_cache_3117_);
lean_dec(v_canon_3102_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3133_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_inc(v_a_3097_);
v___x_3122_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3118_, v_e_3022_, v_a_3097_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_cache_3117_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 9, v___x_3124_);
v___x_3126_ = v___x_3115_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_share_3103_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_maxFVar_3104_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_proofInstInfo_3105_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_inferType_3106_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_getLevel_3107_);
lean_ctor_set(v_reuseFailAlloc_3131_, 5, v_congrInfo_3108_);
lean_ctor_set(v_reuseFailAlloc_3131_, 6, v_defEqI_3109_);
lean_ctor_set(v_reuseFailAlloc_3131_, 7, v_extensions_3110_);
lean_ctor_set(v_reuseFailAlloc_3131_, 8, v_issues_3111_);
lean_ctor_set(v_reuseFailAlloc_3131_, 9, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 10, v_instanceOverrides_3112_);
lean_ctor_set_uint8(v_reuseFailAlloc_3131_, sizeof(void*)*11, v_debug_3113_);
v___x_3126_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_st_ref_put(v_a_3025_, v___x_3126_);
if (v_isShared_3100_ == 0)
{
v___x_3129_ = v___x_3099_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3097_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3096_;
}
}
}
}
case 6:
{
if (v_a_3023_ == 0)
{
lean_object* v___x_3136_; lean_object* v_canon_3137_; lean_object* v_cache_3138_; lean_object* v___x_3139_; 
v___x_3136_ = lean_st_ref_get(v_a_3025_);
v_canon_3137_ = lean_ctor_get(v___x_3136_, 9);
lean_inc_ref(v_canon_3137_);
lean_dec(v___x_3136_);
v_cache_3138_ = lean_ctor_get(v_canon_3137_, 0);
lean_inc_ref(v_cache_3138_);
lean_dec_ref(v_canon_3137_);
v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3138_, v_e_3022_);
lean_dec_ref(v_cache_3138_);
if (lean_obj_tag(v___x_3139_) == 1)
{
lean_object* v_val_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_val_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_val_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v___x_3148_; 
lean_dec(v___x_3139_);
lean_inc_ref(v_e_3022_);
v___x_3148_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3187_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3187_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3187_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v_canon_3154_; lean_object* v_share_3155_; lean_object* v_maxFVar_3156_; lean_object* v_proofInstInfo_3157_; lean_object* v_inferType_3158_; lean_object* v_getLevel_3159_; lean_object* v_congrInfo_3160_; lean_object* v_defEqI_3161_; lean_object* v_extensions_3162_; lean_object* v_issues_3163_; lean_object* v_instanceOverrides_3164_; uint8_t v_debug_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3186_; 
v___x_3153_ = lean_st_ref_take(v_a_3025_);
v_canon_3154_ = lean_ctor_get(v___x_3153_, 9);
v_share_3155_ = lean_ctor_get(v___x_3153_, 0);
v_maxFVar_3156_ = lean_ctor_get(v___x_3153_, 1);
v_proofInstInfo_3157_ = lean_ctor_get(v___x_3153_, 2);
v_inferType_3158_ = lean_ctor_get(v___x_3153_, 3);
v_getLevel_3159_ = lean_ctor_get(v___x_3153_, 4);
v_congrInfo_3160_ = lean_ctor_get(v___x_3153_, 5);
v_defEqI_3161_ = lean_ctor_get(v___x_3153_, 6);
v_extensions_3162_ = lean_ctor_get(v___x_3153_, 7);
v_issues_3163_ = lean_ctor_get(v___x_3153_, 8);
v_instanceOverrides_3164_ = lean_ctor_get(v___x_3153_, 10);
v_debug_3165_ = lean_ctor_get_uint8(v___x_3153_, sizeof(void*)*11);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3167_ = v___x_3153_;
v_isShared_3168_ = v_isSharedCheck_3186_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_instanceOverrides_3164_);
lean_inc(v_canon_3154_);
lean_inc(v_issues_3163_);
lean_inc(v_extensions_3162_);
lean_inc(v_defEqI_3161_);
lean_inc(v_congrInfo_3160_);
lean_inc(v_getLevel_3159_);
lean_inc(v_inferType_3158_);
lean_inc(v_proofInstInfo_3157_);
lean_inc(v_maxFVar_3156_);
lean_inc(v_share_3155_);
lean_dec(v___x_3153_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3186_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_cache_3169_; lean_object* v_cacheInType_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3185_; 
v_cache_3169_ = lean_ctor_get(v_canon_3154_, 0);
v_cacheInType_3170_ = lean_ctor_get(v_canon_3154_, 1);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_canon_3154_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3172_ = v_canon_3154_;
v_isShared_3173_ = v_isSharedCheck_3185_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_cacheInType_3170_);
lean_inc(v_cache_3169_);
lean_dec(v_canon_3154_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3185_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
lean_inc(v_a_3149_);
v___x_3174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3169_, v_e_3022_, v_a_3149_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_cacheInType_3170_);
v___x_3176_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3178_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 9, v___x_3176_);
v___x_3178_ = v___x_3167_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_share_3155_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_maxFVar_3156_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_proofInstInfo_3157_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_inferType_3158_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_getLevel_3159_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_congrInfo_3160_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_defEqI_3161_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_extensions_3162_);
lean_ctor_set(v_reuseFailAlloc_3183_, 8, v_issues_3163_);
lean_ctor_set(v_reuseFailAlloc_3183_, 9, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3183_, 10, v_instanceOverrides_3164_);
lean_ctor_set_uint8(v_reuseFailAlloc_3183_, sizeof(void*)*11, v_debug_3165_);
v___x_3178_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_st_ref_put(v_a_3025_, v___x_3178_);
if (v_isShared_3152_ == 0)
{
v___x_3181_ = v___x_3151_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3149_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3148_;
}
}
}
else
{
lean_object* v___x_3188_; lean_object* v_canon_3189_; lean_object* v_cacheInType_3190_; lean_object* v___x_3191_; 
v___x_3188_ = lean_st_ref_get(v_a_3025_);
v_canon_3189_ = lean_ctor_get(v___x_3188_, 9);
lean_inc_ref(v_canon_3189_);
lean_dec(v___x_3188_);
v_cacheInType_3190_ = lean_ctor_get(v_canon_3189_, 1);
lean_inc_ref(v_cacheInType_3190_);
lean_dec_ref(v_canon_3189_);
v___x_3191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3190_, v_e_3022_);
lean_dec_ref(v_cacheInType_3190_);
if (lean_obj_tag(v___x_3191_) == 1)
{
lean_object* v_val_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_val_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
lean_ctor_set_tag(v___x_3194_, 0);
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_val_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v___x_3200_; 
lean_dec(v___x_3191_);
lean_inc_ref(v_e_3022_);
v___x_3200_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3239_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3239_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3239_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v_canon_3206_; lean_object* v_share_3207_; lean_object* v_maxFVar_3208_; lean_object* v_proofInstInfo_3209_; lean_object* v_inferType_3210_; lean_object* v_getLevel_3211_; lean_object* v_congrInfo_3212_; lean_object* v_defEqI_3213_; lean_object* v_extensions_3214_; lean_object* v_issues_3215_; lean_object* v_instanceOverrides_3216_; uint8_t v_debug_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3238_; 
v___x_3205_ = lean_st_ref_take(v_a_3025_);
v_canon_3206_ = lean_ctor_get(v___x_3205_, 9);
v_share_3207_ = lean_ctor_get(v___x_3205_, 0);
v_maxFVar_3208_ = lean_ctor_get(v___x_3205_, 1);
v_proofInstInfo_3209_ = lean_ctor_get(v___x_3205_, 2);
v_inferType_3210_ = lean_ctor_get(v___x_3205_, 3);
v_getLevel_3211_ = lean_ctor_get(v___x_3205_, 4);
v_congrInfo_3212_ = lean_ctor_get(v___x_3205_, 5);
v_defEqI_3213_ = lean_ctor_get(v___x_3205_, 6);
v_extensions_3214_ = lean_ctor_get(v___x_3205_, 7);
v_issues_3215_ = lean_ctor_get(v___x_3205_, 8);
v_instanceOverrides_3216_ = lean_ctor_get(v___x_3205_, 10);
v_debug_3217_ = lean_ctor_get_uint8(v___x_3205_, sizeof(void*)*11);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3219_ = v___x_3205_;
v_isShared_3220_ = v_isSharedCheck_3238_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_instanceOverrides_3216_);
lean_inc(v_canon_3206_);
lean_inc(v_issues_3215_);
lean_inc(v_extensions_3214_);
lean_inc(v_defEqI_3213_);
lean_inc(v_congrInfo_3212_);
lean_inc(v_getLevel_3211_);
lean_inc(v_inferType_3210_);
lean_inc(v_proofInstInfo_3209_);
lean_inc(v_maxFVar_3208_);
lean_inc(v_share_3207_);
lean_dec(v___x_3205_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3238_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_cache_3221_; lean_object* v_cacheInType_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3237_; 
v_cache_3221_ = lean_ctor_get(v_canon_3206_, 0);
v_cacheInType_3222_ = lean_ctor_get(v_canon_3206_, 1);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_canon_3206_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3224_ = v_canon_3206_;
v_isShared_3225_ = v_isSharedCheck_3237_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_cacheInType_3222_);
lean_inc(v_cache_3221_);
lean_dec(v_canon_3206_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3237_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
lean_inc(v_a_3201_);
v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3222_, v_e_3022_, v_a_3201_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v___x_3226_);
v___x_3228_ = v___x_3224_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_cache_3221_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3230_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 9, v___x_3228_);
v___x_3230_ = v___x_3219_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_share_3207_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_maxFVar_3208_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_proofInstInfo_3209_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v_inferType_3210_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v_getLevel_3211_);
lean_ctor_set(v_reuseFailAlloc_3235_, 5, v_congrInfo_3212_);
lean_ctor_set(v_reuseFailAlloc_3235_, 6, v_defEqI_3213_);
lean_ctor_set(v_reuseFailAlloc_3235_, 7, v_extensions_3214_);
lean_ctor_set(v_reuseFailAlloc_3235_, 8, v_issues_3215_);
lean_ctor_set(v_reuseFailAlloc_3235_, 9, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3235_, 10, v_instanceOverrides_3216_);
lean_ctor_set_uint8(v_reuseFailAlloc_3235_, sizeof(void*)*11, v_debug_3217_);
v___x_3230_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = lean_st_ref_put(v_a_3025_, v___x_3230_);
if (v_isShared_3204_ == 0)
{
v___x_3233_ = v___x_3203_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3201_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3200_;
}
}
}
}
case 8:
{
lean_object* v___x_3240_; 
v___x_3240_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3023_ == 0)
{
lean_object* v___x_3241_; lean_object* v_canon_3242_; lean_object* v_cache_3243_; lean_object* v___x_3244_; 
v___x_3241_ = lean_st_ref_get(v_a_3025_);
v_canon_3242_ = lean_ctor_get(v___x_3241_, 9);
lean_inc_ref(v_canon_3242_);
lean_dec(v___x_3241_);
v_cache_3243_ = lean_ctor_get(v_canon_3242_, 0);
lean_inc_ref(v_cache_3243_);
lean_dec_ref(v_canon_3242_);
v___x_3244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3243_, v_e_3022_);
lean_dec_ref(v_cache_3243_);
if (lean_obj_tag(v___x_3244_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref_known(v_e_3022_, 4);
v_val_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_val_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set_tag(v___x_3247_, 0);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_val_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
else
{
lean_object* v___x_3253_; 
lean_dec(v___x_3244_);
lean_inc_ref(v_e_3022_);
v___x_3253_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3240_, v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3292_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3292_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3292_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v_canon_3259_; lean_object* v_share_3260_; lean_object* v_maxFVar_3261_; lean_object* v_proofInstInfo_3262_; lean_object* v_inferType_3263_; lean_object* v_getLevel_3264_; lean_object* v_congrInfo_3265_; lean_object* v_defEqI_3266_; lean_object* v_extensions_3267_; lean_object* v_issues_3268_; lean_object* v_instanceOverrides_3269_; uint8_t v_debug_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3291_; 
v___x_3258_ = lean_st_ref_take(v_a_3025_);
v_canon_3259_ = lean_ctor_get(v___x_3258_, 9);
v_share_3260_ = lean_ctor_get(v___x_3258_, 0);
v_maxFVar_3261_ = lean_ctor_get(v___x_3258_, 1);
v_proofInstInfo_3262_ = lean_ctor_get(v___x_3258_, 2);
v_inferType_3263_ = lean_ctor_get(v___x_3258_, 3);
v_getLevel_3264_ = lean_ctor_get(v___x_3258_, 4);
v_congrInfo_3265_ = lean_ctor_get(v___x_3258_, 5);
v_defEqI_3266_ = lean_ctor_get(v___x_3258_, 6);
v_extensions_3267_ = lean_ctor_get(v___x_3258_, 7);
v_issues_3268_ = lean_ctor_get(v___x_3258_, 8);
v_instanceOverrides_3269_ = lean_ctor_get(v___x_3258_, 10);
v_debug_3270_ = lean_ctor_get_uint8(v___x_3258_, sizeof(void*)*11);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3272_ = v___x_3258_;
v_isShared_3273_ = v_isSharedCheck_3291_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_instanceOverrides_3269_);
lean_inc(v_canon_3259_);
lean_inc(v_issues_3268_);
lean_inc(v_extensions_3267_);
lean_inc(v_defEqI_3266_);
lean_inc(v_congrInfo_3265_);
lean_inc(v_getLevel_3264_);
lean_inc(v_inferType_3263_);
lean_inc(v_proofInstInfo_3262_);
lean_inc(v_maxFVar_3261_);
lean_inc(v_share_3260_);
lean_dec(v___x_3258_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3291_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_cache_3274_; lean_object* v_cacheInType_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3290_; 
v_cache_3274_ = lean_ctor_get(v_canon_3259_, 0);
v_cacheInType_3275_ = lean_ctor_get(v_canon_3259_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_canon_3259_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3277_ = v_canon_3259_;
v_isShared_3278_ = v_isSharedCheck_3290_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_cacheInType_3275_);
lean_inc(v_cache_3274_);
lean_dec(v_canon_3259_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3290_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_inc(v_a_3254_);
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3274_, v_e_3022_, v_a_3254_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_cacheInType_3275_);
v___x_3281_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3283_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 9, v___x_3281_);
v___x_3283_ = v___x_3272_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_share_3260_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_maxFVar_3261_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_proofInstInfo_3262_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v_inferType_3263_);
lean_ctor_set(v_reuseFailAlloc_3288_, 4, v_getLevel_3264_);
lean_ctor_set(v_reuseFailAlloc_3288_, 5, v_congrInfo_3265_);
lean_ctor_set(v_reuseFailAlloc_3288_, 6, v_defEqI_3266_);
lean_ctor_set(v_reuseFailAlloc_3288_, 7, v_extensions_3267_);
lean_ctor_set(v_reuseFailAlloc_3288_, 8, v_issues_3268_);
lean_ctor_set(v_reuseFailAlloc_3288_, 9, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3288_, 10, v_instanceOverrides_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*11, v_debug_3270_);
v___x_3283_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = lean_st_ref_put(v_a_3025_, v___x_3283_);
if (v_isShared_3257_ == 0)
{
v___x_3286_ = v___x_3256_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3254_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 4);
return v___x_3253_;
}
}
}
else
{
lean_object* v___x_3293_; lean_object* v_canon_3294_; lean_object* v_cacheInType_3295_; lean_object* v___x_3296_; 
v___x_3293_ = lean_st_ref_get(v_a_3025_);
v_canon_3294_ = lean_ctor_get(v___x_3293_, 9);
lean_inc_ref(v_canon_3294_);
lean_dec(v___x_3293_);
v_cacheInType_3295_ = lean_ctor_get(v_canon_3294_, 1);
lean_inc_ref(v_cacheInType_3295_);
lean_dec_ref(v_canon_3294_);
v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3295_, v_e_3022_);
lean_dec_ref(v_cacheInType_3295_);
if (lean_obj_tag(v___x_3296_) == 1)
{
lean_object* v_val_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref_known(v_e_3022_, 4);
v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_val_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set_tag(v___x_3299_, 0);
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_val_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v___x_3305_; 
lean_dec(v___x_3296_);
lean_inc_ref(v_e_3022_);
v___x_3305_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3240_, v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3344_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v_canon_3311_; lean_object* v_share_3312_; lean_object* v_maxFVar_3313_; lean_object* v_proofInstInfo_3314_; lean_object* v_inferType_3315_; lean_object* v_getLevel_3316_; lean_object* v_congrInfo_3317_; lean_object* v_defEqI_3318_; lean_object* v_extensions_3319_; lean_object* v_issues_3320_; lean_object* v_instanceOverrides_3321_; uint8_t v_debug_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3343_; 
v___x_3310_ = lean_st_ref_take(v_a_3025_);
v_canon_3311_ = lean_ctor_get(v___x_3310_, 9);
v_share_3312_ = lean_ctor_get(v___x_3310_, 0);
v_maxFVar_3313_ = lean_ctor_get(v___x_3310_, 1);
v_proofInstInfo_3314_ = lean_ctor_get(v___x_3310_, 2);
v_inferType_3315_ = lean_ctor_get(v___x_3310_, 3);
v_getLevel_3316_ = lean_ctor_get(v___x_3310_, 4);
v_congrInfo_3317_ = lean_ctor_get(v___x_3310_, 5);
v_defEqI_3318_ = lean_ctor_get(v___x_3310_, 6);
v_extensions_3319_ = lean_ctor_get(v___x_3310_, 7);
v_issues_3320_ = lean_ctor_get(v___x_3310_, 8);
v_instanceOverrides_3321_ = lean_ctor_get(v___x_3310_, 10);
v_debug_3322_ = lean_ctor_get_uint8(v___x_3310_, sizeof(void*)*11);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3324_ = v___x_3310_;
v_isShared_3325_ = v_isSharedCheck_3343_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_instanceOverrides_3321_);
lean_inc(v_canon_3311_);
lean_inc(v_issues_3320_);
lean_inc(v_extensions_3319_);
lean_inc(v_defEqI_3318_);
lean_inc(v_congrInfo_3317_);
lean_inc(v_getLevel_3316_);
lean_inc(v_inferType_3315_);
lean_inc(v_proofInstInfo_3314_);
lean_inc(v_maxFVar_3313_);
lean_inc(v_share_3312_);
lean_dec(v___x_3310_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3343_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_cache_3326_; lean_object* v_cacheInType_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3342_; 
v_cache_3326_ = lean_ctor_get(v_canon_3311_, 0);
v_cacheInType_3327_ = lean_ctor_get(v_canon_3311_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_canon_3311_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3329_ = v_canon_3311_;
v_isShared_3330_ = v_isSharedCheck_3342_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_cacheInType_3327_);
lean_inc(v_cache_3326_);
lean_dec(v_canon_3311_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3342_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_inc(v_a_3306_);
v___x_3331_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3327_, v_e_3022_, v_a_3306_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 1, v___x_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_cache_3326_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3335_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 9, v___x_3333_);
v___x_3335_ = v___x_3324_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_share_3312_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_maxFVar_3313_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_proofInstInfo_3314_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_inferType_3315_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_getLevel_3316_);
lean_ctor_set(v_reuseFailAlloc_3340_, 5, v_congrInfo_3317_);
lean_ctor_set(v_reuseFailAlloc_3340_, 6, v_defEqI_3318_);
lean_ctor_set(v_reuseFailAlloc_3340_, 7, v_extensions_3319_);
lean_ctor_set(v_reuseFailAlloc_3340_, 8, v_issues_3320_);
lean_ctor_set(v_reuseFailAlloc_3340_, 9, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3340_, 10, v_instanceOverrides_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3340_, sizeof(void*)*11, v_debug_3322_);
v___x_3335_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3336_ = lean_st_ref_put(v_a_3025_, v___x_3335_);
if (v_isShared_3309_ == 0)
{
v___x_3338_ = v___x_3308_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3306_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 4);
return v___x_3305_;
}
}
}
}
case 5:
{
if (v_a_3023_ == 0)
{
lean_object* v___x_3345_; lean_object* v_canon_3346_; lean_object* v_cache_3347_; lean_object* v___x_3348_; 
v___x_3345_ = lean_st_ref_get(v_a_3025_);
v_canon_3346_ = lean_ctor_get(v___x_3345_, 9);
lean_inc_ref(v_canon_3346_);
lean_dec(v___x_3345_);
v_cache_3347_ = lean_ctor_get(v_canon_3346_, 0);
lean_inc_ref(v_cache_3347_);
lean_dec_ref(v_canon_3346_);
v___x_3348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3347_, v_e_3022_);
lean_dec_ref(v_cache_3347_);
if (lean_obj_tag(v___x_3348_) == 1)
{
lean_object* v_val_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref_known(v_e_3022_, 2);
v_val_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_val_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 0);
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_val_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v___x_3357_; 
lean_dec(v___x_3348_);
lean_inc_ref(v_e_3022_);
v___x_3357_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3396_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3396_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3396_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v_canon_3363_; lean_object* v_share_3364_; lean_object* v_maxFVar_3365_; lean_object* v_proofInstInfo_3366_; lean_object* v_inferType_3367_; lean_object* v_getLevel_3368_; lean_object* v_congrInfo_3369_; lean_object* v_defEqI_3370_; lean_object* v_extensions_3371_; lean_object* v_issues_3372_; lean_object* v_instanceOverrides_3373_; uint8_t v_debug_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3395_; 
v___x_3362_ = lean_st_ref_take(v_a_3025_);
v_canon_3363_ = lean_ctor_get(v___x_3362_, 9);
v_share_3364_ = lean_ctor_get(v___x_3362_, 0);
v_maxFVar_3365_ = lean_ctor_get(v___x_3362_, 1);
v_proofInstInfo_3366_ = lean_ctor_get(v___x_3362_, 2);
v_inferType_3367_ = lean_ctor_get(v___x_3362_, 3);
v_getLevel_3368_ = lean_ctor_get(v___x_3362_, 4);
v_congrInfo_3369_ = lean_ctor_get(v___x_3362_, 5);
v_defEqI_3370_ = lean_ctor_get(v___x_3362_, 6);
v_extensions_3371_ = lean_ctor_get(v___x_3362_, 7);
v_issues_3372_ = lean_ctor_get(v___x_3362_, 8);
v_instanceOverrides_3373_ = lean_ctor_get(v___x_3362_, 10);
v_debug_3374_ = lean_ctor_get_uint8(v___x_3362_, sizeof(void*)*11);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3376_ = v___x_3362_;
v_isShared_3377_ = v_isSharedCheck_3395_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_instanceOverrides_3373_);
lean_inc(v_canon_3363_);
lean_inc(v_issues_3372_);
lean_inc(v_extensions_3371_);
lean_inc(v_defEqI_3370_);
lean_inc(v_congrInfo_3369_);
lean_inc(v_getLevel_3368_);
lean_inc(v_inferType_3367_);
lean_inc(v_proofInstInfo_3366_);
lean_inc(v_maxFVar_3365_);
lean_inc(v_share_3364_);
lean_dec(v___x_3362_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3395_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_cache_3378_; lean_object* v_cacheInType_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3394_; 
v_cache_3378_ = lean_ctor_get(v_canon_3363_, 0);
v_cacheInType_3379_ = lean_ctor_get(v_canon_3363_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_canon_3363_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3381_ = v_canon_3363_;
v_isShared_3382_ = v_isSharedCheck_3394_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_cacheInType_3379_);
lean_inc(v_cache_3378_);
lean_dec(v_canon_3363_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3394_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_inc(v_a_3358_);
v___x_3383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3378_, v_e_3022_, v_a_3358_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_cacheInType_3379_);
v___x_3385_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 9, v___x_3385_);
v___x_3387_ = v___x_3376_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_share_3364_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_maxFVar_3365_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_proofInstInfo_3366_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_inferType_3367_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_getLevel_3368_);
lean_ctor_set(v_reuseFailAlloc_3392_, 5, v_congrInfo_3369_);
lean_ctor_set(v_reuseFailAlloc_3392_, 6, v_defEqI_3370_);
lean_ctor_set(v_reuseFailAlloc_3392_, 7, v_extensions_3371_);
lean_ctor_set(v_reuseFailAlloc_3392_, 8, v_issues_3372_);
lean_ctor_set(v_reuseFailAlloc_3392_, 9, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3392_, 10, v_instanceOverrides_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3392_, sizeof(void*)*11, v_debug_3374_);
v___x_3387_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = lean_st_ref_put(v_a_3025_, v___x_3387_);
if (v_isShared_3361_ == 0)
{
v___x_3390_ = v___x_3360_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3358_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 2);
return v___x_3357_;
}
}
}
else
{
lean_object* v___x_3397_; lean_object* v_canon_3398_; lean_object* v_cacheInType_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_st_ref_get(v_a_3025_);
v_canon_3398_ = lean_ctor_get(v___x_3397_, 9);
lean_inc_ref(v_canon_3398_);
lean_dec(v___x_3397_);
v_cacheInType_3399_ = lean_ctor_get(v_canon_3398_, 1);
lean_inc_ref(v_cacheInType_3399_);
lean_dec_ref(v_canon_3398_);
v___x_3400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3399_, v_e_3022_);
lean_dec_ref(v_cacheInType_3399_);
if (lean_obj_tag(v___x_3400_) == 1)
{
lean_object* v_val_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref_known(v_e_3022_, 2);
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_val_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 0);
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_val_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v___x_3409_; 
lean_dec(v___x_3400_);
lean_inc_ref(v_e_3022_);
v___x_3409_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3448_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3448_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3448_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v_canon_3415_; lean_object* v_share_3416_; lean_object* v_maxFVar_3417_; lean_object* v_proofInstInfo_3418_; lean_object* v_inferType_3419_; lean_object* v_getLevel_3420_; lean_object* v_congrInfo_3421_; lean_object* v_defEqI_3422_; lean_object* v_extensions_3423_; lean_object* v_issues_3424_; lean_object* v_instanceOverrides_3425_; uint8_t v_debug_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3447_; 
v___x_3414_ = lean_st_ref_take(v_a_3025_);
v_canon_3415_ = lean_ctor_get(v___x_3414_, 9);
v_share_3416_ = lean_ctor_get(v___x_3414_, 0);
v_maxFVar_3417_ = lean_ctor_get(v___x_3414_, 1);
v_proofInstInfo_3418_ = lean_ctor_get(v___x_3414_, 2);
v_inferType_3419_ = lean_ctor_get(v___x_3414_, 3);
v_getLevel_3420_ = lean_ctor_get(v___x_3414_, 4);
v_congrInfo_3421_ = lean_ctor_get(v___x_3414_, 5);
v_defEqI_3422_ = lean_ctor_get(v___x_3414_, 6);
v_extensions_3423_ = lean_ctor_get(v___x_3414_, 7);
v_issues_3424_ = lean_ctor_get(v___x_3414_, 8);
v_instanceOverrides_3425_ = lean_ctor_get(v___x_3414_, 10);
v_debug_3426_ = lean_ctor_get_uint8(v___x_3414_, sizeof(void*)*11);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3428_ = v___x_3414_;
v_isShared_3429_ = v_isSharedCheck_3447_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_instanceOverrides_3425_);
lean_inc(v_canon_3415_);
lean_inc(v_issues_3424_);
lean_inc(v_extensions_3423_);
lean_inc(v_defEqI_3422_);
lean_inc(v_congrInfo_3421_);
lean_inc(v_getLevel_3420_);
lean_inc(v_inferType_3419_);
lean_inc(v_proofInstInfo_3418_);
lean_inc(v_maxFVar_3417_);
lean_inc(v_share_3416_);
lean_dec(v___x_3414_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3447_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_cache_3430_; lean_object* v_cacheInType_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3446_; 
v_cache_3430_ = lean_ctor_get(v_canon_3415_, 0);
v_cacheInType_3431_ = lean_ctor_get(v_canon_3415_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_canon_3415_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3433_ = v_canon_3415_;
v_isShared_3434_ = v_isSharedCheck_3446_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_cacheInType_3431_);
lean_inc(v_cache_3430_);
lean_dec(v_canon_3415_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3446_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_inc(v_a_3410_);
v___x_3435_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3431_, v_e_3022_, v_a_3410_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_cache_3430_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 9, v___x_3437_);
v___x_3439_ = v___x_3428_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_share_3416_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_maxFVar_3417_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_proofInstInfo_3418_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_inferType_3419_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_getLevel_3420_);
lean_ctor_set(v_reuseFailAlloc_3444_, 5, v_congrInfo_3421_);
lean_ctor_set(v_reuseFailAlloc_3444_, 6, v_defEqI_3422_);
lean_ctor_set(v_reuseFailAlloc_3444_, 7, v_extensions_3423_);
lean_ctor_set(v_reuseFailAlloc_3444_, 8, v_issues_3424_);
lean_ctor_set(v_reuseFailAlloc_3444_, 9, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3444_, 10, v_instanceOverrides_3425_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, sizeof(void*)*11, v_debug_3426_);
v___x_3439_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_st_ref_put(v_a_3025_, v___x_3439_);
if (v_isShared_3413_ == 0)
{
v___x_3442_ = v___x_3412_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3410_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 2);
return v___x_3409_;
}
}
}
}
case 11:
{
if (v_a_3023_ == 0)
{
lean_object* v___x_3449_; lean_object* v_canon_3450_; lean_object* v_cache_3451_; lean_object* v___x_3452_; 
v___x_3449_ = lean_st_ref_get(v_a_3025_);
v_canon_3450_ = lean_ctor_get(v___x_3449_, 9);
lean_inc_ref(v_canon_3450_);
lean_dec(v___x_3449_);
v_cache_3451_ = lean_ctor_get(v_canon_3450_, 0);
lean_inc_ref(v_cache_3451_);
lean_dec_ref(v_canon_3450_);
v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3451_, v_e_3022_);
lean_dec_ref(v_cache_3451_);
if (lean_obj_tag(v___x_3452_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_val_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 0);
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_val_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
else
{
lean_object* v___x_3461_; 
lean_dec(v___x_3452_);
lean_inc_ref(v_e_3022_);
v___x_3461_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3500_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3500_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3500_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v_canon_3467_; lean_object* v_share_3468_; lean_object* v_maxFVar_3469_; lean_object* v_proofInstInfo_3470_; lean_object* v_inferType_3471_; lean_object* v_getLevel_3472_; lean_object* v_congrInfo_3473_; lean_object* v_defEqI_3474_; lean_object* v_extensions_3475_; lean_object* v_issues_3476_; lean_object* v_instanceOverrides_3477_; uint8_t v_debug_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3499_; 
v___x_3466_ = lean_st_ref_take(v_a_3025_);
v_canon_3467_ = lean_ctor_get(v___x_3466_, 9);
v_share_3468_ = lean_ctor_get(v___x_3466_, 0);
v_maxFVar_3469_ = lean_ctor_get(v___x_3466_, 1);
v_proofInstInfo_3470_ = lean_ctor_get(v___x_3466_, 2);
v_inferType_3471_ = lean_ctor_get(v___x_3466_, 3);
v_getLevel_3472_ = lean_ctor_get(v___x_3466_, 4);
v_congrInfo_3473_ = lean_ctor_get(v___x_3466_, 5);
v_defEqI_3474_ = lean_ctor_get(v___x_3466_, 6);
v_extensions_3475_ = lean_ctor_get(v___x_3466_, 7);
v_issues_3476_ = lean_ctor_get(v___x_3466_, 8);
v_instanceOverrides_3477_ = lean_ctor_get(v___x_3466_, 10);
v_debug_3478_ = lean_ctor_get_uint8(v___x_3466_, sizeof(void*)*11);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3480_ = v___x_3466_;
v_isShared_3481_ = v_isSharedCheck_3499_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_instanceOverrides_3477_);
lean_inc(v_canon_3467_);
lean_inc(v_issues_3476_);
lean_inc(v_extensions_3475_);
lean_inc(v_defEqI_3474_);
lean_inc(v_congrInfo_3473_);
lean_inc(v_getLevel_3472_);
lean_inc(v_inferType_3471_);
lean_inc(v_proofInstInfo_3470_);
lean_inc(v_maxFVar_3469_);
lean_inc(v_share_3468_);
lean_dec(v___x_3466_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3499_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_cache_3482_; lean_object* v_cacheInType_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3498_; 
v_cache_3482_ = lean_ctor_get(v_canon_3467_, 0);
v_cacheInType_3483_ = lean_ctor_get(v_canon_3467_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_canon_3467_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3485_ = v_canon_3467_;
v_isShared_3486_ = v_isSharedCheck_3498_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_cacheInType_3483_);
lean_inc(v_cache_3482_);
lean_dec(v_canon_3467_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3498_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
lean_inc(v_a_3462_);
v___x_3487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3482_, v_e_3022_, v_a_3462_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3487_);
v___x_3489_ = v___x_3485_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_cacheInType_3483_);
v___x_3489_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3491_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 9, v___x_3489_);
v___x_3491_ = v___x_3480_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_share_3468_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_maxFVar_3469_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_proofInstInfo_3470_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_inferType_3471_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_getLevel_3472_);
lean_ctor_set(v_reuseFailAlloc_3496_, 5, v_congrInfo_3473_);
lean_ctor_set(v_reuseFailAlloc_3496_, 6, v_defEqI_3474_);
lean_ctor_set(v_reuseFailAlloc_3496_, 7, v_extensions_3475_);
lean_ctor_set(v_reuseFailAlloc_3496_, 8, v_issues_3476_);
lean_ctor_set(v_reuseFailAlloc_3496_, 9, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 10, v_instanceOverrides_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3496_, sizeof(void*)*11, v_debug_3478_);
v___x_3491_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_st_ref_put(v_a_3025_, v___x_3491_);
if (v_isShared_3465_ == 0)
{
v___x_3494_ = v___x_3464_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3462_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3461_;
}
}
}
else
{
lean_object* v___x_3501_; lean_object* v_canon_3502_; lean_object* v_cacheInType_3503_; lean_object* v___x_3504_; 
v___x_3501_ = lean_st_ref_get(v_a_3025_);
v_canon_3502_ = lean_ctor_get(v___x_3501_, 9);
lean_inc_ref(v_canon_3502_);
lean_dec(v___x_3501_);
v_cacheInType_3503_ = lean_ctor_get(v_canon_3502_, 1);
lean_inc_ref(v_cacheInType_3503_);
lean_dec_ref(v_canon_3502_);
v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3503_, v_e_3022_);
lean_dec_ref(v_cacheInType_3503_);
if (lean_obj_tag(v___x_3504_) == 1)
{
lean_object* v_val_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref_known(v_e_3022_, 3);
v_val_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_val_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set_tag(v___x_3507_, 0);
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_val_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v___x_3504_);
lean_inc_ref(v_e_3022_);
v___x_3513_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3552_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3552_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3552_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v_canon_3519_; lean_object* v_share_3520_; lean_object* v_maxFVar_3521_; lean_object* v_proofInstInfo_3522_; lean_object* v_inferType_3523_; lean_object* v_getLevel_3524_; lean_object* v_congrInfo_3525_; lean_object* v_defEqI_3526_; lean_object* v_extensions_3527_; lean_object* v_issues_3528_; lean_object* v_instanceOverrides_3529_; uint8_t v_debug_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3551_; 
v___x_3518_ = lean_st_ref_take(v_a_3025_);
v_canon_3519_ = lean_ctor_get(v___x_3518_, 9);
v_share_3520_ = lean_ctor_get(v___x_3518_, 0);
v_maxFVar_3521_ = lean_ctor_get(v___x_3518_, 1);
v_proofInstInfo_3522_ = lean_ctor_get(v___x_3518_, 2);
v_inferType_3523_ = lean_ctor_get(v___x_3518_, 3);
v_getLevel_3524_ = lean_ctor_get(v___x_3518_, 4);
v_congrInfo_3525_ = lean_ctor_get(v___x_3518_, 5);
v_defEqI_3526_ = lean_ctor_get(v___x_3518_, 6);
v_extensions_3527_ = lean_ctor_get(v___x_3518_, 7);
v_issues_3528_ = lean_ctor_get(v___x_3518_, 8);
v_instanceOverrides_3529_ = lean_ctor_get(v___x_3518_, 10);
v_debug_3530_ = lean_ctor_get_uint8(v___x_3518_, sizeof(void*)*11);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3532_ = v___x_3518_;
v_isShared_3533_ = v_isSharedCheck_3551_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_instanceOverrides_3529_);
lean_inc(v_canon_3519_);
lean_inc(v_issues_3528_);
lean_inc(v_extensions_3527_);
lean_inc(v_defEqI_3526_);
lean_inc(v_congrInfo_3525_);
lean_inc(v_getLevel_3524_);
lean_inc(v_inferType_3523_);
lean_inc(v_proofInstInfo_3522_);
lean_inc(v_maxFVar_3521_);
lean_inc(v_share_3520_);
lean_dec(v___x_3518_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3551_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_cache_3534_; lean_object* v_cacheInType_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3550_; 
v_cache_3534_ = lean_ctor_get(v_canon_3519_, 0);
v_cacheInType_3535_ = lean_ctor_get(v_canon_3519_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_canon_3519_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3537_ = v_canon_3519_;
v_isShared_3538_ = v_isSharedCheck_3550_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_cacheInType_3535_);
lean_inc(v_cache_3534_);
lean_dec(v_canon_3519_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3550_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
lean_inc(v_a_3514_);
v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3535_, v_e_3022_, v_a_3514_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v___x_3539_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_cache_3534_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 9, v___x_3541_);
v___x_3543_ = v___x_3532_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_share_3520_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_maxFVar_3521_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_proofInstInfo_3522_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_inferType_3523_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_getLevel_3524_);
lean_ctor_set(v_reuseFailAlloc_3548_, 5, v_congrInfo_3525_);
lean_ctor_set(v_reuseFailAlloc_3548_, 6, v_defEqI_3526_);
lean_ctor_set(v_reuseFailAlloc_3548_, 7, v_extensions_3527_);
lean_ctor_set(v_reuseFailAlloc_3548_, 8, v_issues_3528_);
lean_ctor_set(v_reuseFailAlloc_3548_, 9, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3548_, 10, v_instanceOverrides_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3548_, sizeof(void*)*11, v_debug_3530_);
v___x_3543_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_st_ref_put(v_a_3025_, v___x_3543_);
if (v_isShared_3517_ == 0)
{
v___x_3546_ = v___x_3516_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3514_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 3);
return v___x_3513_;
}
}
}
}
case 10:
{
lean_object* v_data_3553_; lean_object* v_expr_3554_; lean_object* v___x_3555_; 
v_data_3553_ = lean_ctor_get(v_e_3022_, 0);
v_expr_3554_ = lean_ctor_get(v_e_3022_, 1);
lean_inc_ref(v_expr_3554_);
v___x_3555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3554_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3570_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3570_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3570_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
size_t v___x_3560_; size_t v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = lean_ptr_addr(v_expr_3554_);
v___x_3561_ = lean_ptr_addr(v_a_3556_);
v___x_3562_ = lean_usize_dec_eq(v___x_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
lean_inc(v_data_3553_);
lean_dec_ref_known(v_e_3022_, 2);
v___x_3563_ = l_Lean_Expr_mdata___override(v_data_3553_, v_a_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3563_);
v___x_3565_ = v___x_3558_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
else
{
lean_object* v___x_3568_; 
lean_dec(v_a_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v_e_3022_);
v___x_3568_ = v___x_3558_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_e_3022_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3022_, 2);
return v___x_3555_;
}
}
default: 
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_e_3022_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3572_, uint8_t v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
if (v_a_3573_ == 0)
{
uint8_t v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = 1;
lean_inc_ref(v_e_3572_);
v___x_3582_ = l_Lean_Meta_isProp(v_e_3572_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; uint8_t v___x_3584_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = lean_unbox(v_a_3583_);
lean_dec(v_a_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3572_, v___x_3581_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; 
v___x_3586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3586_;
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v_e_3572_);
v_a_3587_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3582_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3582_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v___x_3595_; 
v___x_3595_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3596_, lean_object* v_e_3597_, uint8_t v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
if (lean_obj_tag(v_e_3597_) == 7)
{
lean_object* v_binderName_3606_; lean_object* v_binderType_3607_; lean_object* v_body_3608_; uint8_t v_binderInfo_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_binderName_3606_ = lean_ctor_get(v_e_3597_, 0);
lean_inc(v_binderName_3606_);
v_binderType_3607_ = lean_ctor_get(v_e_3597_, 1);
lean_inc_ref(v_binderType_3607_);
v_body_3608_ = lean_ctor_get(v_e_3597_, 2);
lean_inc_ref(v_body_3608_);
v_binderInfo_3609_ = lean_ctor_get_uint8(v_e_3597_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3597_, 3);
lean_inc_ref(v_fvars_3596_);
v___f_3610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3610_, 0, v_fvars_3596_);
lean_closure_set(v___f_3610_, 1, v_body_3608_);
v___x_3611_ = lean_expr_instantiate_rev(v_binderType_3607_, v_fvars_3596_);
lean_dec_ref(v_fvars_3596_);
lean_dec_ref(v_binderType_3607_);
v___x_3612_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3611_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = 0;
v___x_3615_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_3606_, v_binderInfo_3609_, v_a_3613_, v___f_3610_, v___x_3614_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
return v___x_3615_;
}
else
{
lean_dec_ref(v___f_3610_);
lean_dec(v_binderName_3606_);
return v___x_3612_;
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_expr_instantiate_rev(v_e_3597_, v_fvars_3596_);
lean_dec_ref(v_e_3597_);
v___x_3617_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3616_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; uint8_t v___x_3619_; uint8_t v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = 0;
v___x_3620_ = 1;
v___x_3621_ = 1;
v___x_3622_ = l_Lean_Meta_mkForallFVars(v_fvars_3596_, v_a_3618_, v___x_3619_, v___x_3620_, v___x_3620_, v___x_3621_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec_ref(v_fvars_3596_);
return v___x_3622_;
}
else
{
lean_dec_ref(v_fvars_3596_);
return v___x_3617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3623_, lean_object* v_body_3624_, lean_object* v_x_3625_, uint8_t v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_array_push(v_fvars_3623_, v_x_3625_);
v___x_3635_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3634_, v_body_3624_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
uint8_t v_a_boxed_3645_; lean_object* v_res_3646_; 
v_a_boxed_3645_ = lean_unbox(v_a_3637_);
v_res_3646_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3636_, v_a_boxed_3645_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
uint8_t v_a_boxed_3656_; lean_object* v_res_3657_; 
v_a_boxed_3656_ = lean_unbox(v_a_3648_);
v_res_3657_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3647_, v_a_boxed_3656_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v_a_boxed_3667_; lean_object* v_res_3668_; 
v_a_boxed_3667_ = lean_unbox(v_a_3659_);
v_res_3668_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3658_, v_a_boxed_3667_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
uint8_t v_a_boxed_3678_; lean_object* v_res_3679_; 
v_a_boxed_3678_ = lean_unbox(v_a_3670_);
v_res_3679_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3669_, v_a_boxed_3678_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
uint8_t v_a_boxed_3689_; lean_object* v_res_3690_; 
v_a_boxed_3689_ = lean_unbox(v_a_3681_);
v_res_3690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3680_, v_a_boxed_3689_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3691_, lean_object* v_e_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
uint8_t v_a_boxed_3701_; lean_object* v_res_3702_; 
v_a_boxed_3701_ = lean_unbox(v_a_3693_);
v_res_3702_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3691_, v_e_3692_, v_a_boxed_3701_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3703_, lean_object* v_e_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
uint8_t v_a_boxed_3713_; lean_object* v_res_3714_; 
v_a_boxed_3713_ = lean_unbox(v_a_3705_);
v_res_3714_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3703_, v_e_3704_, v_a_boxed_3713_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3715_, lean_object* v_report_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
uint8_t v_report_boxed_3725_; uint8_t v_a_boxed_3726_; lean_object* v_res_3727_; 
v_report_boxed_3725_ = lean_unbox(v_report_3716_);
v_a_boxed_3726_ = lean_unbox(v_a_3717_);
v_res_3727_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3715_, v_report_boxed_3725_, v_a_boxed_3726_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_a_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
uint8_t v_a_boxed_3737_; lean_object* v_res_3738_; 
v_a_boxed_3737_ = lean_unbox(v_a_3729_);
v_res_3738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3728_, v_a_boxed_3737_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3739_, lean_object* v_e_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
uint8_t v_a_boxed_3749_; lean_object* v_res_3750_; 
v_a_boxed_3749_ = lean_unbox(v_a_3741_);
v_res_3750_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3739_, v_e_3740_, v_a_boxed_3749_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3751_, lean_object* v_00_u03b1_3752_, lean_object* v_c_3753_, lean_object* v_a_3754_, lean_object* v_b_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
uint8_t v_a_boxed_3764_; lean_object* v_res_3765_; 
v_a_boxed_3764_ = lean_unbox(v_a_3756_);
v_res_3765_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3751_, v_00_u03b1_3752_, v_c_3753_, v_a_3754_, v_b_3755_, v_a_boxed_3764_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3766_, lean_object* v_00_u03b1_3767_, lean_object* v_c_3768_, lean_object* v_inst_3769_, lean_object* v_a_3770_, lean_object* v_b_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
uint8_t v_a_boxed_3780_; lean_object* v_res_3781_; 
v_a_boxed_3780_ = lean_unbox(v_a_3772_);
v_res_3781_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3766_, v_00_u03b1_3767_, v_c_3768_, v_inst_3769_, v_a_3770_, v_b_3771_, v_a_boxed_3780_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
uint8_t v_a_boxed_3791_; lean_object* v_res_3792_; 
v_a_boxed_3791_ = lean_unbox(v_a_3783_);
v_res_3792_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3782_, v_a_boxed_3791_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
uint8_t v_a_boxed_3802_; lean_object* v_res_3803_; 
v_a_boxed_3802_ = lean_unbox(v_a_3794_);
v_res_3803_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3793_, v_a_boxed_3802_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3804_, lean_object* v_prop_3805_, lean_object* v_inst_3806_, lean_object* v_e_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
uint8_t v_a_boxed_3816_; lean_object* v_res_3817_; 
v_a_boxed_3816_ = lean_unbox(v_a_3808_);
v_res_3817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3804_, v_prop_3805_, v_inst_3806_, v_e_3807_, v_a_boxed_3816_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3818_, lean_object* v_report_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
uint8_t v_report_boxed_3828_; uint8_t v_a_boxed_3829_; lean_object* v_res_3830_; 
v_report_boxed_3828_ = lean_unbox(v_report_3819_);
v_a_boxed_3829_ = lean_unbox(v_a_3820_);
v_res_3830_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3818_, v_report_boxed_3828_, v_a_boxed_3829_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3831_, lean_object* v_prop_3832_, lean_object* v_h_3833_, lean_object* v_e_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
uint8_t v_a_boxed_3843_; lean_object* v_res_3844_; 
v_a_boxed_3843_ = lean_unbox(v_a_3835_);
v_res_3844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3831_, v_prop_3832_, v_h_3833_, v_e_3834_, v_a_boxed_3843_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_3845_, lean_object* v_snd_3846_, lean_object* v_a_3847_, lean_object* v___x_3848_, lean_object* v_fst_3849_, lean_object* v___x_3850_, lean_object* v_____r_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
uint8_t v___x_62204__boxed_3860_; uint8_t v___y_62207__boxed_3861_; lean_object* v_res_3862_; 
v___x_62204__boxed_3860_ = lean_unbox(v___x_3848_);
v___y_62207__boxed_3861_ = lean_unbox(v___y_3852_);
v_res_3862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_3845_, v_snd_3846_, v_a_3847_, v___x_62204__boxed_3860_, v_fst_3849_, v___x_3850_, v_____r_3851_, v___y_62207__boxed_3861_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec_ref(v___x_3850_);
lean_dec(v_a_3847_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
uint8_t v_a_boxed_3872_; lean_object* v_res_3873_; 
v_a_boxed_3872_ = lean_unbox(v_a_3864_);
v_res_3873_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3863_, v_a_boxed_3872_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
uint8_t v_a_boxed_3883_; lean_object* v_res_3884_; 
v_a_boxed_3883_ = lean_unbox(v_a_3875_);
v_res_3884_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_3874_, v_a_boxed_3883_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3885_, lean_object* v___x_3886_, lean_object* v_a_3887_, lean_object* v_b_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
uint8_t v___y_62410__boxed_3897_; lean_object* v_res_3898_; 
v___y_62410__boxed_3897_ = lean_unbox(v___y_3889_);
v_res_3898_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3885_, v___x_3886_, v_a_3887_, v_b_3888_, v___y_62410__boxed_3897_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___x_3886_);
lean_dec(v_upperBound_3885_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3899_, lean_object* v_prop_3900_, lean_object* v_h_3901_, lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
uint8_t v_a_boxed_3911_; lean_object* v_res_3912_; 
v_a_boxed_3911_ = lean_unbox(v_a_3903_);
v_res_3912_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3899_, v_prop_3900_, v_h_3901_, v_e_3902_, v_a_boxed_3911_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_, lean_object* v_x_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v___y_62523__boxed_3925_; lean_object* v_res_3926_; 
v___y_62523__boxed_3925_ = lean_unbox(v___y_3917_);
v_res_3926_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_3913_, v_x_3914_, v_x_3915_, v_x_3916_, v___y_62523__boxed_3925_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
uint8_t v_a_boxed_3936_; lean_object* v_res_3937_; 
v_a_boxed_3936_ = lean_unbox(v_a_3928_);
v_res_3937_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3927_, v_a_boxed_3936_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3938_, uint8_t v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3938_, v___y_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v___y_65051__boxed_3957_; lean_object* v_res_3958_; 
v___y_65051__boxed_3957_ = lean_unbox(v___y_3949_);
v_res_3958_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3948_, v___y_65051__boxed_3957_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_3959_, uint8_t v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_3959_, v___y_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
uint8_t v___y_65077__boxed_3978_; lean_object* v_res_3979_; 
v___y_65077__boxed_3978_ = lean_unbox(v___y_3970_);
v_res_3979_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_3969_, v___y_65077__boxed_3978_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object* v_00_u03b1_3980_, lean_object* v_name_3981_, lean_object* v_type_3982_, lean_object* v_val_3983_, lean_object* v_k_3984_, uint8_t v_nondep_3985_, uint8_t v_kind_3986_, uint8_t v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_3981_, v_type_3982_, v_val_3983_, v_k_3984_, v_nondep_3985_, v_kind_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object* v_00_u03b1_3996_, lean_object* v_name_3997_, lean_object* v_type_3998_, lean_object* v_val_3999_, lean_object* v_k_4000_, lean_object* v_nondep_4001_, lean_object* v_kind_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
uint8_t v_nondep_boxed_4011_; uint8_t v_kind_boxed_4012_; uint8_t v___y_65103__boxed_4013_; lean_object* v_res_4014_; 
v_nondep_boxed_4011_ = lean_unbox(v_nondep_4001_);
v_kind_boxed_4012_ = lean_unbox(v_kind_4002_);
v___y_65103__boxed_4013_ = lean_unbox(v___y_4003_);
v_res_4014_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(v_00_u03b1_3996_, v_name_3997_, v_type_3998_, v_val_3999_, v_k_4000_, v_nondep_boxed_4011_, v_kind_boxed_4012_, v___y_65103__boxed_4013_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object* v_00_u03b1_4015_, lean_object* v_name_4016_, uint8_t v_bi_4017_, lean_object* v_type_4018_, lean_object* v_k_4019_, uint8_t v_kind_4020_, uint8_t v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_4016_, v_bi_4017_, v_type_4018_, v_k_4019_, v_kind_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object* v_00_u03b1_4030_, lean_object* v_name_4031_, lean_object* v_bi_4032_, lean_object* v_type_4033_, lean_object* v_k_4034_, lean_object* v_kind_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
uint8_t v_bi_boxed_4044_; uint8_t v_kind_boxed_4045_; uint8_t v___y_65129__boxed_4046_; lean_object* v_res_4047_; 
v_bi_boxed_4044_ = lean_unbox(v_bi_4032_);
v_kind_boxed_4045_ = lean_unbox(v_kind_4035_);
v___y_65129__boxed_4046_ = lean_unbox(v___y_4036_);
v_res_4047_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(v_00_u03b1_4030_, v_name_4031_, v_bi_boxed_4044_, v_type_4033_, v_k_4034_, v_kind_boxed_4045_, v___y_65129__boxed_4046_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4048_, lean_object* v_m_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4049_, v_a_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4052_, lean_object* v_m_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4052_, v_m_4053_, v_a_4054_);
lean_dec_ref(v_a_4054_);
lean_dec_ref(v_m_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4056_, lean_object* v_m_4057_, lean_object* v_a_4058_, lean_object* v_b_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4057_, v_a_4058_, v_b_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4061_, lean_object* v_msg_4062_, uint8_t v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4061_, v_msg_4062_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4072_, lean_object* v_msg_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
uint8_t v___y_65159__boxed_4082_; lean_object* v_res_4083_; 
v___y_65159__boxed_4082_ = lean_unbox(v___y_4074_);
v_res_4083_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4072_, v_msg_4073_, v___y_65159__boxed_4082_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4084_, lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_inst_4087_, lean_object* v_R_4088_, lean_object* v_a_4089_, lean_object* v_b_4090_, lean_object* v_c_4091_, uint8_t v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4084_, v___x_4086_, v_a_4089_, v_b_4090_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4101_, lean_object* v___x_4102_, lean_object* v___x_4103_, lean_object* v_inst_4104_, lean_object* v_R_4105_, lean_object* v_a_4106_, lean_object* v_b_4107_, lean_object* v_c_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___y_65189__boxed_4117_; lean_object* v_res_4118_; 
v___y_65189__boxed_4117_ = lean_unbox(v___y_4109_);
v_res_4118_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4101_, v___x_4102_, v___x_4103_, v_inst_4104_, v_R_4105_, v_a_4106_, v_b_4107_, v_c_4108_, v___y_65189__boxed_4117_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec_ref(v___x_4103_);
lean_dec(v___x_4102_);
lean_dec(v_upperBound_4101_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4119_, lean_object* v_a_4120_, lean_object* v_x_4121_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4120_, v_x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4123_, lean_object* v_a_4124_, lean_object* v_x_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4123_, v_a_4124_, v_x_4125_);
lean_dec(v_x_4125_);
lean_dec_ref(v_a_4124_);
return v_res_4126_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4127_, lean_object* v_a_4128_, lean_object* v_x_4129_){
_start:
{
uint8_t v___x_4130_; 
v___x_4130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4128_, v_x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4131_, lean_object* v_a_4132_, lean_object* v_x_4133_){
_start:
{
uint8_t v_res_4134_; lean_object* v_r_4135_; 
v_res_4134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4131_, v_a_4132_, v_x_4133_);
lean_dec(v_x_4133_);
lean_dec_ref(v_a_4132_);
v_r_4135_ = lean_box(v_res_4134_);
return v_r_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4136_, lean_object* v_data_4137_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4139_, lean_object* v_a_4140_, lean_object* v_b_4141_, lean_object* v_x_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4140_, v_b_4141_, v_x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object* v_00_u03b2_4144_, lean_object* v_i_4145_, lean_object* v_source_4146_, lean_object* v_target_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v_i_4145_, v_source_4146_, v_target_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object* v_00_u03b2_4149_, lean_object* v_x_4150_, lean_object* v_x_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_x_4150_, v_x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4153_, lean_object* v_i_4154_, lean_object* v_arg_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4153_, v_i_4154_, v_arg_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4177_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
uint8_t v___x_4166_; 
v___x_4166_ = lean_unbox(v_a_4162_);
lean_dec(v_a_4162_);
if (v___x_4166_ == 3)
{
uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4167_ = 0;
v___x_4168_ = lean_box(v___x_4167_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4168_);
v___x_4170_ = v___x_4164_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
else
{
uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4172_ = 1;
v___x_4173_ = lean_box(v___x_4172_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4173_);
v___x_4175_ = v___x_4164_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
v_a_4178_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4161_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4161_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4186_, lean_object* v_i_4187_, lean_object* v_arg_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4186_, v_i_4187_, v_arg_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_i_4187_);
lean_dec_ref(v_pinfos_4186_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4195_, lean_object* v_opts_4196_, lean_object* v_act_4197_, lean_object* v_decl_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_inc(v___y_4204_);
lean_inc_ref(v___y_4203_);
lean_inc(v___y_4202_);
lean_inc_ref(v___y_4201_);
lean_inc(v___y_4200_);
lean_inc_ref(v___y_4199_);
v___x_4206_ = lean_apply_6(v_act_4197_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
v___x_4207_ = l_Lean_profileitIOUnsafe___redArg(v_category_4195_, v_opts_4196_, v___x_4206_, v_decl_4198_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4208_, lean_object* v_opts_4209_, lean_object* v_act_4210_, lean_object* v_decl_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4208_, v_opts_4209_, v_act_4210_, v_decl_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v_opts_4209_);
lean_dec_ref(v_category_4208_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4220_, lean_object* v_category_4221_, lean_object* v_opts_4222_, lean_object* v_act_4223_, lean_object* v_decl_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4221_, v_opts_4222_, v_act_4223_, v_decl_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4233_, lean_object* v_category_4234_, lean_object* v_opts_4235_, lean_object* v_act_4236_, lean_object* v_decl_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4233_, v_category_4234_, v_opts_4235_, v_act_4236_, v_decl_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec_ref(v_opts_4235_);
lean_dec_ref(v_category_4234_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4246_, lean_object* v_e_4247_, uint8_t v___x_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___y_4257_; lean_object* v___x_4266_; uint8_t v_transparency_4267_; uint8_t v___x_4268_; 
v___x_4266_ = l_Lean_Meta_Context_config(v___y_4251_);
v_transparency_4267_ = lean_ctor_get_uint8(v___x_4266_, 9);
lean_dec_ref(v___x_4266_);
v___x_4268_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4267_, v___x_4246_);
if (v___x_4268_ == 0)
{
lean_object* v_keyedConfig_4269_; uint8_t v_trackZetaDelta_4270_; lean_object* v_zetaDeltaSet_4271_; lean_object* v_lctx_4272_; lean_object* v_localInstances_4273_; lean_object* v_defEqCtx_x3f_4274_; lean_object* v_synthPendingDepth_4275_; lean_object* v_customCanUnfoldPredicate_x3f_4276_; uint8_t v_univApprox_4277_; uint8_t v_inTypeClassResolution_4278_; uint8_t v_cacheInferType_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v_keyedConfig_4269_ = lean_ctor_get(v___y_4251_, 0);
v_trackZetaDelta_4270_ = lean_ctor_get_uint8(v___y_4251_, sizeof(void*)*7);
v_zetaDeltaSet_4271_ = lean_ctor_get(v___y_4251_, 1);
v_lctx_4272_ = lean_ctor_get(v___y_4251_, 2);
v_localInstances_4273_ = lean_ctor_get(v___y_4251_, 3);
v_defEqCtx_x3f_4274_ = lean_ctor_get(v___y_4251_, 4);
v_synthPendingDepth_4275_ = lean_ctor_get(v___y_4251_, 5);
v_customCanUnfoldPredicate_x3f_4276_ = lean_ctor_get(v___y_4251_, 6);
v_univApprox_4277_ = lean_ctor_get_uint8(v___y_4251_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4278_ = lean_ctor_get_uint8(v___y_4251_, sizeof(void*)*7 + 2);
v_cacheInferType_4279_ = lean_ctor_get_uint8(v___y_4251_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4269_);
v___x_4280_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4246_, v_keyedConfig_4269_);
lean_inc(v_customCanUnfoldPredicate_x3f_4276_);
lean_inc(v_synthPendingDepth_4275_);
lean_inc(v_defEqCtx_x3f_4274_);
lean_inc_ref(v_localInstances_4273_);
lean_inc_ref(v_lctx_4272_);
lean_inc(v_zetaDeltaSet_4271_);
v___x_4281_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
lean_ctor_set(v___x_4281_, 1, v_zetaDeltaSet_4271_);
lean_ctor_set(v___x_4281_, 2, v_lctx_4272_);
lean_ctor_set(v___x_4281_, 3, v_localInstances_4273_);
lean_ctor_set(v___x_4281_, 4, v_defEqCtx_x3f_4274_);
lean_ctor_set(v___x_4281_, 5, v_synthPendingDepth_4275_);
lean_ctor_set(v___x_4281_, 6, v_customCanUnfoldPredicate_x3f_4276_);
lean_ctor_set_uint8(v___x_4281_, sizeof(void*)*7, v_trackZetaDelta_4270_);
lean_ctor_set_uint8(v___x_4281_, sizeof(void*)*7 + 1, v_univApprox_4277_);
lean_ctor_set_uint8(v___x_4281_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4278_);
lean_ctor_set_uint8(v___x_4281_, sizeof(void*)*7 + 3, v_cacheInferType_4279_);
v___x_4282_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4247_, v___x_4248_, v___y_4249_, v___y_4250_, v___x_4281_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec_ref_known(v___x_4281_, 7);
v___y_4257_ = v___x_4282_;
goto v___jp_4256_;
}
else
{
lean_object* v___x_4283_; 
v___x_4283_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4247_, v___x_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
v___y_4257_ = v___x_4283_;
goto v___jp_4256_;
}
v___jp_4256_:
{
if (lean_obj_tag(v___y_4257_) == 0)
{
return v___y_4257_;
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_a_4258_ = lean_ctor_get(v___y_4257_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___y_4257_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___y_4257_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___y_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4284_, lean_object* v_e_4285_, lean_object* v___x_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
uint8_t v___x_2117__boxed_4294_; uint8_t v___x_2118__boxed_4295_; lean_object* v_res_4296_; 
v___x_2117__boxed_4294_ = lean_unbox(v___x_4284_);
v___x_2118__boxed_4295_ = lean_unbox(v___x_4286_);
v_res_4296_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2117__boxed_4294_, v_e_4285_, v___x_2118__boxed_4295_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; uint8_t v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___f_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4306_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4303_);
v___x_4307_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4308_ = 0;
v___x_4309_ = 2;
v___x_4310_ = lean_box(v___x_4309_);
v___x_4311_ = lean_box(v___x_4308_);
v___f_4312_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4312_, 0, v___x_4310_);
lean_closure_set(v___f_4312_, 1, v_e_4298_);
lean_closure_set(v___f_4312_, 2, v___x_4311_);
v___x_4313_ = lean_box(0);
v___x_4314_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4307_, v___x_4306_, v___f_4312_, v___x_4313_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec_ref(v___x_4306_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Lean_Meta_Sym_canon(v_e_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
return v_res_4323_;
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

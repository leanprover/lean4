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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t l_Lean_Expr_isCharLit(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2____boxed(lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
return v_res_84_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(lean_object* v_args_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
uint8_t v___y_106_; lean_object* v___y_107_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v_args_141_; uint8_t v_modified_142_; lean_object* v___y_143_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v_modified_173_; 
v___x_171_ = lean_array_get_size(v_args_96_);
v___x_172_ = lean_unsigned_to_nat(3u);
v_modified_173_ = lean_nat_dec_eq(v___x_171_, v___x_172_);
if (v_modified_173_ == 0)
{
lean_dec_ref(v_args_96_);
goto v___jp_102_;
}
else
{
uint8_t v_modified_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_modified_174_ = 0;
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_array_fget_borrowed(v_args_96_, v___x_175_);
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_178_ = l_Lean_Expr_isAppOf(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
v_args_141_ = v_args_96_;
v_modified_142_ = v_modified_174_;
v___y_143_ = v_a_98_;
goto v___jp_140_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_getNatValue_x3f(v___x_176_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
if (lean_obj_tag(v_a_180_) == 1)
{
lean_object* v_val_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_val_181_ = lean_ctor_get(v_a_180_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_a_180_, 1);
v___x_182_ = l_Lean_mkRawNatLit(v_val_181_);
v___x_183_ = lean_array_fset(v_args_96_, v___x_175_, v___x_182_);
v_args_141_ = v___x_183_;
v_modified_142_ = v_modified_173_;
v___y_143_ = v_a_98_;
goto v___jp_140_;
}
else
{
lean_dec(v_a_180_);
v_args_141_ = v_args_96_;
v_modified_142_ = v_modified_174_;
v___y_143_ = v_a_98_;
goto v___jp_140_;
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v_args_96_);
v_a_184_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_179_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_179_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
v___jp_105_:
{
if (v___y_106_ == 0)
{
lean_dec_ref(v___y_107_);
goto v___jp_102_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___y_107_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
v___jp_110_:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_114_, v___y_111_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_131_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_131_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_unbox(v_a_116_);
lean_dec(v_a_116_);
if (v___x_120_ == 0)
{
lean_del_object(v___x_118_);
v___y_106_ = v___y_112_;
v___y_107_ = v___y_113_;
goto v___jp_105_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_array_fget_borrowed(v___y_113_, v___x_121_);
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_124_ = l_Lean_Expr_isConstOf(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_125_ = l_Lean_Int_mkType;
v___x_126_ = lean_array_fset(v___y_113_, v___x_121_, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_127_);
v___x_129_ = v___x_118_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_del_object(v___x_118_);
v___y_106_ = v___y_112_;
v___y_107_ = v___y_113_;
goto v___jp_105_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v___y_113_);
v_a_132_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_115_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_115_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
v___jp_140_:
{
lean_object* v___x_144_; lean_object* v_inst_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(2u);
v_inst_145_ = lean_array_fget_borrowed(v_args_141_, v___x_144_);
lean_inc(v_inst_145_);
v___x_146_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_145_, v___y_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_162_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_162_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_162_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_162_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_a_147_);
lean_dec(v_a_147_);
if (v___x_151_ == 0)
{
lean_inc(v_inst_145_);
lean_del_object(v___x_149_);
v___y_111_ = v___y_143_;
v___y_112_ = v_modified_142_;
v___y_113_ = v_args_141_;
v___y_114_ = v_inst_145_;
goto v___jp_110_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_fget_borrowed(v_args_141_, v___x_152_);
v___x_154_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_156_ = l_Lean_Nat_mkType;
v___x_157_ = lean_array_fset(v_args_141_, v___x_152_, v___x_156_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_158_);
v___x_160_ = v___x_149_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_inc(v_inst_145_);
lean_del_object(v___x_149_);
v___y_111_ = v___y_143_;
v___y_112_ = v_modified_142_;
v___y_113_ = v_args_141_;
v___y_114_ = v_inst_145_;
goto v___jp_110_;
}
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec_ref(v_args_141_);
v_a_163_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_146_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_146_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_96_ = stack[0].m_obj;
lean_object* v_a_97_ = stack[1].m_obj;
lean_object* v_a_98_ = stack[2].m_obj;
lean_object* v_a_99_ = stack[3].m_obj;
lean_object* v_a_100_ = stack[4].m_obj;
lean_object* v_res_192_;
v_res_192_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_args_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(lean_object* v_args_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_args_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1));
v___x_205_ = l_Lean_mkConst(v___x_204_, v___x_203_);
return v___x_205_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(lean_object* v_e_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_getBitVecValue_x3f(v_e_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_251_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_251_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_251_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_251_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
if (lean_obj_tag(v_a_213_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_246_; 
lean_del_object(v___x_215_);
v_val_217_ = lean_ctor_get(v_a_213_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_246_ == 0)
{
v___x_219_ = v_a_213_;
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_val_217_);
lean_dec(v_a_213_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_fst_221_ = lean_ctor_get(v_val_217_, 0);
lean_inc(v_fst_221_);
v_snd_222_ = lean_ctor_get(v_val_217_, 1);
lean_inc(v_snd_222_);
lean_dec(v_val_217_);
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2);
v___x_224_ = l_Lean_mkNatLit(v_fst_221_);
v___x_225_ = l_Lean_Expr_app___override(v___x_223_, v___x_224_);
v___x_226_ = l_Lean_Meta_mkNumeral(v___x_225_, v_snd_222_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_237_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v_a_227_);
v___x_232_ = v___x_219_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_232_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_del_object(v___x_219_);
v_a_238_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_226_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_226_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_a_213_);
v___x_247_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_247_);
v___x_249_ = v___x_215_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_212_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_212_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_206_ = stack[0].m_obj;
lean_object* v_a_207_ = stack[1].m_obj;
lean_object* v_a_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_a_210_ = stack[4].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___boxed(lean_object* v_e_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
return v_res_267_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7));
v___x_287_ = l_Lean_mkConst(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_box(0);
v___x_289_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_290_ = l_Lean_mkConst(v___x_289_, v___x_288_);
return v___x_290_;
}
}
lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_300_; 
lean_inc_ref(v_e_291_);
v___x_300_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_291_, v_a_293_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_509_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_509_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_509_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_509_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = l_Lean_Expr_cleanupAnnotations(v_a_301_);
v___x_306_ = l_Lean_Expr_isApp(v___x_305_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_305_);
lean_del_object(v___x_303_);
lean_dec_ref(v_e_291_);
goto v___jp_297_;
}
else
{
lean_object* v_arg_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_arg_307_ = lean_ctor_get(v___x_305_, 1);
lean_inc_ref(v_arg_307_);
v___x_308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_305_);
v___x_309_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_310_ = l_Lean_Expr_isConstOf(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
uint8_t v___x_311_; 
lean_del_object(v___x_303_);
v___x_311_ = l_Lean_Expr_isApp(v___x_308_);
if (v___x_311_ == 0)
{
lean_dec_ref(v___x_308_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_e_291_);
goto v___jp_297_;
}
else
{
lean_object* v_arg_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_arg_312_ = lean_ctor_get(v___x_308_, 1);
lean_inc_ref(v_arg_312_);
v___x_313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_308_);
v___x_314_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_315_ = l_Lean_Expr_isConstOf(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = l_Lean_Expr_isApp(v___x_313_);
if (v___x_316_ == 0)
{
lean_dec_ref(v___x_313_);
lean_dec_ref(v_arg_312_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_e_291_);
goto v___jp_297_;
}
else
{
lean_object* v_arg_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_arg_317_ = lean_ctor_get(v___x_313_, 1);
lean_inc_ref(v_arg_317_);
v___x_318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_313_);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_320_ = l_Lean_Expr_isConstOf(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_dec_ref(v_arg_312_);
v___x_321_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_318_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
lean_dec_ref(v_arg_317_);
lean_dec_ref(v_arg_307_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_318_, v___x_323_);
lean_dec_ref(v___x_318_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_e_291_);
goto v___jp_297_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_325_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec_ref(v___x_318_);
lean_dec_ref(v_e_291_);
v___x_326_ = l_Lean_Meta_getNatValue_x3f(v_arg_317_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_317_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_389_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_389_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_389_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_389_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
if (lean_obj_tag(v_a_327_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_332_; 
lean_del_object(v___x_329_);
v_val_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v_a_327_, 1);
v___x_332_ = l_Lean_Meta_getNatValue_x3f(v_arg_307_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_307_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_376_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_376_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
if (lean_obj_tag(v_a_333_) == 1)
{
lean_object* v_val_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_371_; 
v_val_337_ = lean_ctor_get(v_a_333_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_a_333_);
if (v_isSharedCheck_371_ == 0)
{
v___x_339_ = v_a_333_;
v_isShared_340_ = v_isSharedCheck_371_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_val_337_);
lean_dec(v_a_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_371_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_nat_dec_eq(v_val_331_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_del_object(v___x_335_);
v___x_343_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8);
lean_inc(v_val_331_);
v___x_344_ = l_Lean_mkNatLit(v_val_331_);
v___x_345_ = l_Lean_Expr_app___override(v___x_343_, v___x_344_);
v___x_346_ = lean_nat_mod(v_val_337_, v_val_331_);
lean_dec(v_val_331_);
lean_dec(v_val_337_);
v___x_347_ = l_Lean_Meta_mkNumeral(v___x_345_, v___x_346_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_358_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_a_348_);
v___x_353_ = v___x_339_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_del_object(v___x_339_);
v_a_359_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_347_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_347_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
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
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_del_object(v___x_339_);
lean_dec(v_val_337_);
lean_dec(v_val_331_);
v___x_367_ = lean_box(0);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_367_);
v___x_369_ = v___x_335_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec(v_a_333_);
lean_dec(v_val_331_);
v___x_372_ = lean_box(0);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_372_);
v___x_374_ = v___x_335_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_val_331_);
v_a_377_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_332_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_332_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_dec(v_a_327_);
lean_dec_ref(v_arg_307_);
v___x_385_ = lean_box(0);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_385_);
v___x_387_ = v___x_329_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_arg_307_);
v_a_390_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_326_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_326_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_318_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_e_291_);
lean_inc_ref(v_arg_317_);
v___x_398_ = l_Lean_Meta_getLitValueModulus_x3f(v_arg_317_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_460_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_460_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_460_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_460_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
if (lean_obj_tag(v_a_399_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_404_; 
v_val_403_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_a_399_, 1);
v___x_404_ = l_Lean_Meta_getNatValue_x3f(v_arg_312_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_312_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_447_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_447_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_447_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_447_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
if (lean_obj_tag(v_a_405_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_442_; 
lean_del_object(v___x_401_);
v_val_414_ = lean_ctor_get(v_a_405_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_442_ == 0)
{
v___x_416_ = v_a_405_;
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v_a_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_nat_dec_eq(v_val_403_, v___x_418_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = lean_nat_dec_lt(v_val_414_, v_val_403_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_del_object(v___x_407_);
v___x_421_ = lean_nat_mod(v_val_414_, v_val_403_);
lean_dec(v_val_403_);
lean_dec(v_val_414_);
v___x_422_ = l_Lean_Meta_mkNumeral(v_arg_317_, v___x_421_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_423_);
v___x_428_ = v___x_416_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_430_ = v___x_425_;
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
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_416_);
v_a_434_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_422_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_422_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_del_object(v___x_416_);
lean_dec(v_val_414_);
lean_dec(v_val_403_);
lean_dec_ref(v_arg_317_);
goto v___jp_409_;
}
}
else
{
lean_del_object(v___x_416_);
lean_dec(v_val_414_);
lean_dec(v_val_403_);
lean_dec_ref(v_arg_317_);
goto v___jp_409_;
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_del_object(v___x_407_);
lean_dec(v_a_405_);
lean_dec(v_val_403_);
lean_dec_ref(v_arg_317_);
v___x_443_ = lean_box(0);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_443_);
v___x_445_ = v___x_401_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
v___jp_409_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_box(0);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
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
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_val_403_);
lean_del_object(v___x_401_);
lean_dec_ref(v_arg_317_);
v_a_448_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_404_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_404_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec(v_a_399_);
lean_dec_ref(v_arg_317_);
lean_dec_ref(v_arg_312_);
v___x_456_ = lean_box(0);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_456_);
v___x_458_ = v___x_401_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_arg_317_);
lean_dec_ref(v_arg_312_);
v_a_461_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_398_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_398_);
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
else
{
lean_object* v___x_469_; 
lean_dec_ref(v___x_313_);
lean_dec_ref(v_arg_312_);
lean_dec_ref(v_arg_307_);
v___x_469_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_469_;
}
}
}
else
{
uint8_t v___x_470_; 
lean_dec_ref(v___x_308_);
v___x_470_ = l_Lean_Expr_isCharLit(v_e_291_);
lean_dec_ref(v_e_291_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_del_object(v___x_303_);
v___x_471_ = l_Lean_Meta_getNatValue_x3f(v_arg_307_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_307_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_496_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_496_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 1)
{
lean_object* v_val_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_491_; 
v_val_476_ = lean_ctor_get(v_a_472_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_491_ == 0)
{
v___x_478_ = v_a_472_;
v_isShared_479_ = v_isSharedCheck_491_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_val_476_);
lean_dec(v_a_472_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_491_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint32_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_480_ = l_Char_ofNat(v_val_476_);
lean_dec(v_val_476_);
v___x_481_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9);
v___x_482_ = lean_uint32_to_nat(v___x_480_);
v___x_483_ = l_Lean_mkRawNatLit(v___x_482_);
v___x_484_ = l_Lean_Expr_app___override(v___x_481_, v___x_483_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_484_);
v___x_486_ = v___x_478_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_486_);
v___x_488_ = v___x_474_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_a_472_);
v___x_492_ = lean_box(0);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_492_);
v___x_494_ = v___x_474_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_471_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_471_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec_ref(v_arg_307_);
v___x_505_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_505_);
v___x_507_ = v___x_303_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_e_291_);
v_a_510_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_300_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_300_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
v___jp_297_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Canon_normNumLit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_291_ = stack[0].m_obj;
lean_object* v_a_292_ = stack[1].m_obj;
lean_object* v_a_293_ = stack[2].m_obj;
lean_object* v_a_294_ = stack[3].m_obj;
lean_object* v_a_295_ = stack[4].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_525_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_528_, lean_object* v_k_529_, uint8_t v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_530_ == 0)
{
lean_object* v___x_540_; lean_object* v_canon_541_; lean_object* v_cache_542_; lean_object* v___x_543_; 
v___x_540_ = lean_st_ref_get(v_a_532_);
v_canon_541_ = lean_ctor_get(v___x_540_, 10);
lean_inc_ref(v_canon_541_);
lean_dec(v___x_540_);
v_cache_542_ = lean_ctor_get(v_canon_541_, 0);
lean_inc_ref(v_cache_542_);
lean_dec_ref(v_canon_541_);
lean_inc_ref(v_e_528_);
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_538_, v___x_539_, v_cache_542_, v_e_528_);
lean_dec_ref(v_cache_542_);
if (lean_obj_tag(v___x_543_) == 1)
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_k_529_);
lean_dec_ref(v_e_528_);
v_val_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_val_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_543_);
v___x_552_ = lean_box(v_a_530_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_553_ = lean_apply_8(v_k_529_, v___x_552_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, lean_box(0));
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_593_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_593_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_593_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_593_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v_canon_559_; lean_object* v_share_560_; lean_object* v_maxFVar_561_; lean_object* v_proofInstInfo_562_; lean_object* v_proofInstInfoFVar_563_; lean_object* v_inferType_564_; lean_object* v_getLevel_565_; lean_object* v_congrInfo_566_; lean_object* v_defEqI_567_; lean_object* v_extensions_568_; lean_object* v_issues_569_; lean_object* v_instanceOverrides_570_; uint8_t v_debug_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_592_; 
v___x_558_ = lean_st_ref_take(v_a_532_);
v_canon_559_ = lean_ctor_get(v___x_558_, 10);
v_share_560_ = lean_ctor_get(v___x_558_, 0);
v_maxFVar_561_ = lean_ctor_get(v___x_558_, 1);
v_proofInstInfo_562_ = lean_ctor_get(v___x_558_, 2);
v_proofInstInfoFVar_563_ = lean_ctor_get(v___x_558_, 3);
v_inferType_564_ = lean_ctor_get(v___x_558_, 4);
v_getLevel_565_ = lean_ctor_get(v___x_558_, 5);
v_congrInfo_566_ = lean_ctor_get(v___x_558_, 6);
v_defEqI_567_ = lean_ctor_get(v___x_558_, 7);
v_extensions_568_ = lean_ctor_get(v___x_558_, 8);
v_issues_569_ = lean_ctor_get(v___x_558_, 9);
v_instanceOverrides_570_ = lean_ctor_get(v___x_558_, 11);
v_debug_571_ = lean_ctor_get_uint8(v___x_558_, sizeof(void*)*12);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_592_ == 0)
{
v___x_573_ = v___x_558_;
v_isShared_574_ = v_isSharedCheck_592_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_instanceOverrides_570_);
lean_inc(v_canon_559_);
lean_inc(v_issues_569_);
lean_inc(v_extensions_568_);
lean_inc(v_defEqI_567_);
lean_inc(v_congrInfo_566_);
lean_inc(v_getLevel_565_);
lean_inc(v_inferType_564_);
lean_inc(v_proofInstInfoFVar_563_);
lean_inc(v_proofInstInfo_562_);
lean_inc(v_maxFVar_561_);
lean_inc(v_share_560_);
lean_dec(v___x_558_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_592_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_cache_575_; lean_object* v_cacheInType_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_591_; 
v_cache_575_ = lean_ctor_get(v_canon_559_, 0);
v_cacheInType_576_ = lean_ctor_get(v_canon_559_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_canon_559_);
if (v_isSharedCheck_591_ == 0)
{
v___x_578_ = v_canon_559_;
v_isShared_579_ = v_isSharedCheck_591_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_cacheInType_576_);
lean_inc(v_cache_575_);
lean_dec(v_canon_559_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_591_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_inc(v_a_554_);
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_538_, v___x_539_, v_cache_575_, v_e_528_, v_a_554_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_cacheInType_576_);
v___x_582_ = v_reuseFailAlloc_590_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 10, v___x_582_);
v___x_584_ = v___x_573_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_share_560_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_maxFVar_561_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_proofInstInfo_562_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_proofInstInfoFVar_563_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_inferType_564_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_getLevel_565_);
lean_ctor_set(v_reuseFailAlloc_589_, 6, v_congrInfo_566_);
lean_ctor_set(v_reuseFailAlloc_589_, 7, v_defEqI_567_);
lean_ctor_set(v_reuseFailAlloc_589_, 8, v_extensions_568_);
lean_ctor_set(v_reuseFailAlloc_589_, 9, v_issues_569_);
lean_ctor_set(v_reuseFailAlloc_589_, 10, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_589_, 11, v_instanceOverrides_570_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*12, v_debug_571_);
v___x_584_ = v_reuseFailAlloc_589_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_st_ref_put(v_a_532_, v___x_584_);
if (v_isShared_557_ == 0)
{
v___x_587_ = v___x_556_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_554_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_528_);
return v___x_553_;
}
}
}
else
{
lean_object* v___x_594_; lean_object* v_canon_595_; lean_object* v_cacheInType_596_; lean_object* v___x_597_; 
v___x_594_ = lean_st_ref_get(v_a_532_);
v_canon_595_ = lean_ctor_get(v___x_594_, 10);
lean_inc_ref(v_canon_595_);
lean_dec(v___x_594_);
v_cacheInType_596_ = lean_ctor_get(v_canon_595_, 1);
lean_inc_ref(v_cacheInType_596_);
lean_dec_ref(v_canon_595_);
lean_inc_ref(v_e_528_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_538_, v___x_539_, v_cacheInType_596_, v_e_528_);
lean_dec_ref(v_cacheInType_596_);
if (lean_obj_tag(v___x_597_) == 1)
{
lean_object* v_val_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_k_529_);
lean_dec_ref(v_e_528_);
v_val_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_val_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 0);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_val_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_597_);
v___x_606_ = lean_box(v_a_530_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_607_ = lean_apply_8(v_k_529_, v___x_606_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_647_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_647_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_647_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_647_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v_canon_613_; lean_object* v_share_614_; lean_object* v_maxFVar_615_; lean_object* v_proofInstInfo_616_; lean_object* v_proofInstInfoFVar_617_; lean_object* v_inferType_618_; lean_object* v_getLevel_619_; lean_object* v_congrInfo_620_; lean_object* v_defEqI_621_; lean_object* v_extensions_622_; lean_object* v_issues_623_; lean_object* v_instanceOverrides_624_; uint8_t v_debug_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_646_; 
v___x_612_ = lean_st_ref_take(v_a_532_);
v_canon_613_ = lean_ctor_get(v___x_612_, 10);
v_share_614_ = lean_ctor_get(v___x_612_, 0);
v_maxFVar_615_ = lean_ctor_get(v___x_612_, 1);
v_proofInstInfo_616_ = lean_ctor_get(v___x_612_, 2);
v_proofInstInfoFVar_617_ = lean_ctor_get(v___x_612_, 3);
v_inferType_618_ = lean_ctor_get(v___x_612_, 4);
v_getLevel_619_ = lean_ctor_get(v___x_612_, 5);
v_congrInfo_620_ = lean_ctor_get(v___x_612_, 6);
v_defEqI_621_ = lean_ctor_get(v___x_612_, 7);
v_extensions_622_ = lean_ctor_get(v___x_612_, 8);
v_issues_623_ = lean_ctor_get(v___x_612_, 9);
v_instanceOverrides_624_ = lean_ctor_get(v___x_612_, 11);
v_debug_625_ = lean_ctor_get_uint8(v___x_612_, sizeof(void*)*12);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_646_ == 0)
{
v___x_627_ = v___x_612_;
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_instanceOverrides_624_);
lean_inc(v_canon_613_);
lean_inc(v_issues_623_);
lean_inc(v_extensions_622_);
lean_inc(v_defEqI_621_);
lean_inc(v_congrInfo_620_);
lean_inc(v_getLevel_619_);
lean_inc(v_inferType_618_);
lean_inc(v_proofInstInfoFVar_617_);
lean_inc(v_proofInstInfo_616_);
lean_inc(v_maxFVar_615_);
lean_inc(v_share_614_);
lean_dec(v___x_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_cache_629_; lean_object* v_cacheInType_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_645_; 
v_cache_629_ = lean_ctor_get(v_canon_613_, 0);
v_cacheInType_630_ = lean_ctor_get(v_canon_613_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_canon_613_);
if (v_isSharedCheck_645_ == 0)
{
v___x_632_ = v_canon_613_;
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_cacheInType_630_);
lean_inc(v_cache_629_);
lean_dec(v_canon_613_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc(v_a_608_);
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_538_, v___x_539_, v_cacheInType_630_, v_e_528_, v_a_608_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_cache_629_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_644_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 10, v___x_636_);
v___x_638_ = v___x_627_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_share_614_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_maxFVar_615_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_proofInstInfo_616_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_proofInstInfoFVar_617_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_inferType_618_);
lean_ctor_set(v_reuseFailAlloc_643_, 5, v_getLevel_619_);
lean_ctor_set(v_reuseFailAlloc_643_, 6, v_congrInfo_620_);
lean_ctor_set(v_reuseFailAlloc_643_, 7, v_defEqI_621_);
lean_ctor_set(v_reuseFailAlloc_643_, 8, v_extensions_622_);
lean_ctor_set(v_reuseFailAlloc_643_, 9, v_issues_623_);
lean_ctor_set(v_reuseFailAlloc_643_, 10, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_643_, 11, v_instanceOverrides_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_643_, sizeof(void*)*12, v_debug_625_);
v___x_638_ = v_reuseFailAlloc_643_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_st_ref_put(v_a_532_, v___x_638_);
if (v_isShared_611_ == 0)
{
v___x_641_ = v___x_610_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_608_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_528_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_528_ = stack[0].m_obj;
lean_object* v_k_529_ = stack[1].m_obj;
uint8_t v_a_530_ = stack[2].m_num;
lean_object* v_a_531_ = stack[3].m_obj;
lean_object* v_a_532_ = stack[4].m_obj;
lean_object* v_a_533_ = stack[5].m_obj;
lean_object* v_a_534_ = stack[6].m_obj;
lean_object* v_a_535_ = stack[7].m_obj;
lean_object* v_a_536_ = stack[8].m_obj;
lean_object* v_res_648_;
v_res_648_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_528_, v_k_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_649_, lean_object* v_k_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
uint8_t v_a_boxed_659_; lean_object* v_res_660_; 
v_a_boxed_659_ = lean_unbox(v_a_651_);
v_res_660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_649_, v_k_650_, v_a_boxed_659_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_660_;
}
}
uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_668_ = l_Lean_Expr_cleanupAnnotations(v_e_667_);
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_670_ = l_Lean_Expr_isConstOf(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_Expr_isApp(v___x_668_);
if (v___x_671_ == 0)
{
lean_dec_ref(v___x_668_);
return v___x_671_;
}
else
{
lean_object* v_arg_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_arg_672_ = lean_ctor_get(v___x_668_, 1);
lean_inc_ref(v_arg_672_);
v___x_673_ = l_Lean_Expr_appFnCleanup___redArg(v___x_668_);
v___x_674_ = l_Lean_Expr_isApp(v___x_673_);
if (v___x_674_ == 0)
{
lean_dec_ref(v___x_673_);
lean_dec_ref(v_arg_672_);
return v___x_674_;
}
else
{
lean_object* v_arg_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_arg_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc_ref(v_arg_675_);
v___x_676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_673_);
v___x_677_ = l_Lean_Expr_isApp(v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v___x_676_);
lean_dec_ref(v_arg_675_);
lean_dec_ref(v_arg_672_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_676_);
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_680_ = l_Lean_Expr_isConstOf(v___x_678_, v___x_679_);
lean_dec_ref(v___x_678_);
if (v___x_680_ == 0)
{
lean_dec_ref(v_arg_675_);
lean_dec_ref(v_arg_672_);
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = l_Lean_Expr_isBoolTrue(v_arg_675_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_arg_672_);
return v___x_681_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_Expr_isBoolTrue(v_arg_672_);
return v___x_682_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_668_);
return v___x_670_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_667_ = stack[0].m_obj;
uint8_t v_res_683_;
v_res_683_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_667_);
stack->m_num = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_691_ = l_Lean_Expr_cleanupAnnotations(v_e_690_);
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_693_ = l_Lean_Expr_isConstOf(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_Expr_isApp(v___x_691_);
if (v___x_694_ == 0)
{
lean_dec_ref(v___x_691_);
return v___x_694_;
}
else
{
lean_object* v_arg_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_arg_695_ = lean_ctor_get(v___x_691_, 1);
lean_inc_ref(v_arg_695_);
v___x_696_ = l_Lean_Expr_appFnCleanup___redArg(v___x_691_);
v___x_697_ = l_Lean_Expr_isApp(v___x_696_);
if (v___x_697_ == 0)
{
lean_dec_ref(v___x_696_);
lean_dec_ref(v_arg_695_);
return v___x_697_;
}
else
{
lean_object* v_arg_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_arg_698_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref(v_arg_698_);
v___x_699_ = l_Lean_Expr_appFnCleanup___redArg(v___x_696_);
v___x_700_ = l_Lean_Expr_isApp(v___x_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v___x_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_695_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_699_);
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_703_ = l_Lean_Expr_isConstOf(v___x_701_, v___x_702_);
lean_dec_ref(v___x_701_);
if (v___x_703_ == 0)
{
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_695_);
return v___x_703_;
}
else
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Expr_isBoolFalse(v_arg_698_);
if (v___x_704_ == 0)
{
lean_dec_ref(v_arg_695_);
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Expr_isBoolTrue(v_arg_695_);
return v___x_705_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_691_);
return v___x_693_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_690_ = stack[0].m_obj;
uint8_t v_res_706_;
v_res_706_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_690_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_707_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t v_x_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(v_x_710_);
v___x_712_ = lean_obj_tag_nat(v___x_711_);
lean_dec(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_710_ = stack[0].m_num;
lean_object* v_res_713_;
v_res_713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_710_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object* v_x_714_){
_start:
{
uint8_t v_x_4__boxed_715_; lean_object* v_res_716_; 
v_x_4__boxed_715_ = lean_unbox(v_x_714_);
v_res_716_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_4__boxed_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_717_){
_start:
{
lean_inc(v_k_717_);
return v_k_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_718_);
lean_dec(v_k_718_);
return v_res_719_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_720_, lean_object* v_ctorIdx_721_, uint8_t v_t_722_, lean_object* v_h_723_, lean_object* v_k_724_){
_start:
{
lean_inc(v_k_724_);
return v_k_724_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_721_ = stack[1].m_obj;
uint8_t v_t_722_ = stack[2].m_num;
lean_object* v_k_724_ = stack[4].m_obj;
lean_object* v_res_725_;
v_res_725_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_box(0), v_ctorIdx_721_, v_t_722_, lean_box(0), v_k_724_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_726_, lean_object* v_ctorIdx_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_k_730_){
_start:
{
uint8_t v_t_boxed_731_; lean_object* v_res_732_; 
v_t_boxed_731_ = lean_unbox(v_t_728_);
v_res_732_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_726_, v_ctorIdx_727_, v_t_boxed_731_, v_h_729_, v_k_730_);
lean_dec(v_k_730_);
lean_dec(v_ctorIdx_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_733_){
_start:
{
lean_inc(v_canonType_733_);
return v_canonType_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_734_);
lean_dec(v_canonType_734_);
return v_res_735_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_736_, uint8_t v_t_737_, lean_object* v_h_738_, lean_object* v_canonType_739_){
_start:
{
lean_inc(v_canonType_739_);
return v_canonType_739_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_737_ = stack[1].m_num;
lean_object* v_canonType_739_ = stack[3].m_obj;
lean_object* v_res_740_;
v_res_740_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_box(0), v_t_737_, lean_box(0), v_canonType_739_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_741_, lean_object* v_t_742_, lean_object* v_h_743_, lean_object* v_canonType_744_){
_start:
{
uint8_t v_t_boxed_745_; lean_object* v_res_746_; 
v_t_boxed_745_ = lean_unbox(v_t_742_);
v_res_746_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_741_, v_t_boxed_745_, v_h_743_, v_canonType_744_);
lean_dec(v_canonType_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_747_){
_start:
{
lean_inc(v_canonInst_747_);
return v_canonInst_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_748_);
lean_dec(v_canonInst_748_);
return v_res_749_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_750_, uint8_t v_t_751_, lean_object* v_h_752_, lean_object* v_canonInst_753_){
_start:
{
lean_inc(v_canonInst_753_);
return v_canonInst_753_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_751_ = stack[1].m_num;
lean_object* v_canonInst_753_ = stack[3].m_obj;
lean_object* v_res_754_;
v_res_754_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_box(0), v_t_751_, lean_box(0), v_canonInst_753_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_canonInst_758_){
_start:
{
uint8_t v_t_boxed_759_; lean_object* v_res_760_; 
v_t_boxed_759_ = lean_unbox(v_t_756_);
v_res_760_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_755_, v_t_boxed_759_, v_h_757_, v_canonInst_758_);
lean_dec(v_canonInst_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_761_){
_start:
{
lean_inc(v_canonImplicit_761_);
return v_canonImplicit_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_762_);
lean_dec(v_canonImplicit_762_);
return v_res_763_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_764_, uint8_t v_t_765_, lean_object* v_h_766_, lean_object* v_canonImplicit_767_){
_start:
{
lean_inc(v_canonImplicit_767_);
return v_canonImplicit_767_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_765_ = stack[1].m_num;
lean_object* v_canonImplicit_767_ = stack[3].m_obj;
lean_object* v_res_768_;
v_res_768_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_box(0), v_t_765_, lean_box(0), v_canonImplicit_767_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_canonImplicit_772_){
_start:
{
uint8_t v_t_boxed_773_; lean_object* v_res_774_; 
v_t_boxed_773_ = lean_unbox(v_t_770_);
v_res_774_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_769_, v_t_boxed_773_, v_h_771_, v_canonImplicit_772_);
lean_dec(v_canonImplicit_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_775_){
_start:
{
lean_inc(v_visit_775_);
return v_visit_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_776_);
lean_dec(v_visit_776_);
return v_res_777_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_778_, uint8_t v_t_779_, lean_object* v_h_780_, lean_object* v_visit_781_){
_start:
{
lean_inc(v_visit_781_);
return v_visit_781_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_779_ = stack[1].m_num;
lean_object* v_visit_781_ = stack[3].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_box(0), v_t_779_, lean_box(0), v_visit_781_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_visit_786_){
_start:
{
uint8_t v_t_boxed_787_; lean_object* v_res_788_; 
v_t_boxed_787_ = lean_unbox(v_t_784_);
v_res_788_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_783_, v_t_boxed_787_, v_h_785_, v_visit_786_);
lean_dec(v_visit_786_);
return v_res_788_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = 0;
return v___x_790_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_803_, lean_object* v_x_804_){
_start:
{
switch(v_r_803_)
{
case 0:
{
lean_object* v___x_805_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_805_;
}
case 1:
{
lean_object* v___x_806_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_806_;
}
case 2:
{
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_807_;
}
default: 
{
lean_object* v___x_808_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_808_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_803_ = stack[0].m_num;
lean_object* v_x_804_ = stack[1].m_obj;
lean_object* v_res_809_;
v_res_809_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_803_, v_x_804_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_810_, lean_object* v_x_811_){
_start:
{
uint8_t v_r_boxed_812_; lean_object* v_res_813_; 
v_r_boxed_812_ = lean_unbox(v_r_810_);
v_res_813_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_812_, v_x_811_);
lean_dec(v_x_811_);
return v_res_813_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_816_, lean_object* v_i_817_, lean_object* v_arg_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_pinfos_816_);
v___x_875_ = lean_nat_dec_lt(v_i_817_, v___x_874_);
if (v___x_875_ == 0)
{
v___y_825_ = v_a_819_;
v___y_826_ = v_a_820_;
v___y_827_ = v_a_821_;
v___y_828_ = v_a_822_;
goto v___jp_824_;
}
else
{
lean_object* v_pinfo_876_; uint8_t v_isInstance_877_; 
v_pinfo_876_ = lean_array_fget_borrowed(v_pinfos_816_, v_i_817_);
v_isInstance_877_ = lean_ctor_get_uint8(v_pinfo_876_, sizeof(void*)*1 + 4);
if (v_isInstance_877_ == 0)
{
uint8_t v_isProp_878_; 
v_isProp_878_ = lean_ctor_get_uint8(v_pinfo_876_, sizeof(void*)*1 + 2);
if (v_isProp_878_ == 0)
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_876_);
if (v___x_879_ == 0)
{
v___y_825_ = v_a_819_;
v___y_826_ = v_a_820_;
v___y_827_ = v_a_821_;
v___y_828_ = v_a_822_;
goto v___jp_824_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_isTypeFormer(v_arg_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_896_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_unbox(v_a_881_);
lean_dec(v_a_881_);
if (v___x_885_ == 0)
{
uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = 2;
v___x_887_ = lean_box(v___x_886_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_887_);
v___x_889_ = v___x_883_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = 0;
v___x_892_ = lean_box(v___x_891_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_892_);
v___x_894_ = v___x_883_;
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
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_880_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_880_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
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
else
{
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v_arg_818_);
v___x_905_ = 3;
v___x_906_ = lean_box(v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
else
{
uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref(v_arg_818_);
v___x_908_ = 1;
v___x_909_ = lean_box(v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
v___jp_824_:
{
lean_object* v___x_829_; 
lean_inc_ref(v_arg_818_);
v___x_829_ = l_Lean_Meta_isProp(v_arg_818_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_865_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_865_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_865_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_865_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v___x_834_; 
v___x_834_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_del_object(v___x_832_);
v___x_835_ = l_Lean_Meta_isTypeFormer(v_arg_818_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_851_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; 
v___x_840_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = 3;
v___x_842_ = lean_box(v___x_841_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = 0;
v___x_847_ = lean_box(v___x_846_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_847_);
v___x_849_ = v___x_838_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_835_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_835_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec_ref(v_arg_818_);
v___x_860_ = 3;
v___x_861_ = lean_box(v___x_860_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_861_);
v___x_863_ = v___x_832_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
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
lean_dec_ref(v_arg_818_);
v_a_866_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_829_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_829_);
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon_0interp(lean_interpreter_value* stack)
{
lean_object* v_pinfos_816_ = stack[0].m_obj;
lean_object* v_i_817_ = stack[1].m_obj;
lean_object* v_arg_818_ = stack[2].m_obj;
lean_object* v_a_819_ = stack[3].m_obj;
lean_object* v_a_820_ = stack[4].m_obj;
lean_object* v_a_821_ = stack[5].m_obj;
lean_object* v_a_822_ = stack[6].m_obj;
lean_object* v_res_911_;
v_res_911_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_816_, v_i_817_, v_arg_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_912_, lean_object* v_i_913_, lean_object* v_arg_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_912_, v_i_913_, v_arg_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_i_913_);
lean_dec_ref(v_pinfos_912_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_921_, lean_object* v_offset_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_nat_dec_eq(v_offset_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = l_Lean_mkNatLit(v_offset_922_);
v___x_926_ = l_Lean_mkNatAdd(v_e_921_, v___x_925_);
return v___x_926_;
}
else
{
lean_dec(v_offset_922_);
return v_e_921_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_927_; lean_object* v_dummy_928_; 
v___x_927_ = lean_box(0);
v_dummy_928_ = l_Lean_Expr_sort___override(v___x_927_);
return v_dummy_928_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_929_, lean_object* v_e_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
uint8_t v_fromClass_936_; 
v_fromClass_936_ = lean_ctor_get_uint8(v_info_929_, sizeof(void*)*3);
if (v_fromClass_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_930_, v_fromClass_936_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_973_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_973_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_973_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_973_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
if (lean_obj_tag(v_a_938_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_940_);
v_val_942_ = lean_ctor_get(v_a_938_, 0);
lean_inc(v_val_942_);
lean_dec_ref_known(v_a_938_, 1);
v___x_943_ = l_Lean_Expr_getAppFn(v_val_942_);
v___x_944_ = l_Lean_Meta_reduceProj_x3f(v___x_943_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
if (lean_obj_tag(v_a_945_) == 0)
{
lean_dec(v_val_942_);
return v___x_944_;
}
else
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_967_; 
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_968_);
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_967_;
goto v_resetjp_946_;
}
else
{
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_967_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_val_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_966_; 
v_val_949_ = lean_ctor_get(v_a_945_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_966_ == 0)
{
v___x_951_ = v_a_945_;
v_isShared_952_ = v_isSharedCheck_966_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_val_949_);
lean_dec(v_a_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_966_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_dummy_953_; lean_object* v_nargs_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v_dummy_953_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_954_ = l_Lean_Expr_getAppNumArgs(v_val_942_);
lean_inc(v_nargs_954_);
v___x_955_ = lean_mk_array(v_nargs_954_, v_dummy_953_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_sub(v_nargs_954_, v___x_956_);
lean_dec(v_nargs_954_);
v___x_958_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_942_, v___x_955_, v___x_957_);
v___x_959_ = l_Lean_mkAppN(v_val_949_, v___x_958_);
lean_dec_ref(v___x_958_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_959_);
v___x_961_ = v___x_951_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_961_);
v___x_963_ = v___x_947_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
else
{
lean_dec(v_val_942_);
return v___x_944_;
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec(v_a_938_);
v___x_969_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_969_);
v___x_971_ = v___x_940_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
return v___x_937_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref(v_e_930_);
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_929_ = stack[0].m_obj;
lean_object* v_e_930_ = stack[1].m_obj;
lean_object* v_a_931_ = stack[2].m_obj;
lean_object* v_a_932_ = stack[3].m_obj;
lean_object* v_a_933_ = stack[4].m_obj;
lean_object* v_a_934_ = stack[5].m_obj;
lean_object* v_res_976_;
v_res_976_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_929_, v_e_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_977_, lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_977_, v_e_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec_ref(v_info_977_);
return v_res_984_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_985_, lean_object* v_e_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_985_, v_e_986_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_994_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_985_ = stack[0].m_obj;
lean_object* v_e_986_ = stack[1].m_obj;
lean_object* v_a_987_ = stack[2].m_obj;
lean_object* v_a_988_ = stack[3].m_obj;
lean_object* v_a_989_ = stack[4].m_obj;
lean_object* v_a_990_ = stack[5].m_obj;
lean_object* v_a_991_ = stack[6].m_obj;
lean_object* v_a_992_ = stack[7].m_obj;
lean_object* v_res_995_;
v_res_995_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_985_, v_e_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_996_, lean_object* v_e_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_996_, v_e_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_info_996_);
return v_res_1005_;
}
}
uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_1006_){
_start:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_1008_ = l_Lean_Expr_isConstOf(v_e_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1006_ = stack[0].m_obj;
uint8_t v_res_1009_;
v_res_1009_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_1006_);
stack->m_num = v_res_1009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_1010_);
lean_dec_ref(v_e_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = l_Lean_Expr_cleanupAnnotations(v_e_1046_);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_1049_ = l_Lean_Expr_isConstOf(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; 
v___x_1050_ = l_Lean_Expr_isApp(v___x_1047_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v___x_1047_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1047_);
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_1053_ = l_Lean_Expr_isConstOf(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
v___x_1054_ = l_Lean_Expr_isApp(v___x_1051_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v___x_1051_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1051_);
v___x_1056_ = l_Lean_Expr_isApp(v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v___x_1055_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1055_);
v___x_1058_ = l_Lean_Expr_isApp(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1057_);
v___x_1060_ = l_Lean_Expr_isApp(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec_ref(v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1059_);
v___x_1062_ = l_Lean_Expr_isApp(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v_arg_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_arg_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc_ref(v_arg_1063_);
v___x_1064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1061_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1066_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1068_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1070_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1074_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1073_);
lean_dec_ref(v___x_1064_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_arg_1063_);
return v___x_1074_;
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1063_);
lean_dec_ref(v_arg_1063_);
return v___x_1075_;
}
}
else
{
uint8_t v___x_1076_; 
lean_dec_ref(v___x_1064_);
v___x_1076_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1063_);
lean_dec_ref(v_arg_1063_);
return v___x_1076_;
}
}
else
{
uint8_t v___x_1077_; 
lean_dec_ref(v___x_1064_);
v___x_1077_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1063_);
lean_dec_ref(v_arg_1063_);
return v___x_1077_;
}
}
else
{
uint8_t v___x_1078_; 
lean_dec_ref(v___x_1064_);
v___x_1078_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1063_);
lean_dec_ref(v_arg_1063_);
return v___x_1078_;
}
}
else
{
uint8_t v___x_1079_; 
lean_dec_ref(v___x_1064_);
v___x_1079_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1063_);
lean_dec_ref(v_arg_1063_);
return v___x_1079_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1051_);
return v___x_1053_;
}
}
}
else
{
lean_dec_ref(v___x_1047_);
return v___x_1049_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1046_ = stack[0].m_obj;
uint8_t v_res_1080_;
v_res_1080_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1046_);
stack->m_num = v_res_1080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1081_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1090_, lean_object* v_inst_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1099_; 
lean_inc_ref(v_inst_1091_);
lean_inc_ref(v_e_1090_);
v___x_1099_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1090_, v_inst_1091_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1150_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1150_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1150_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_unbox(v_a_1100_);
lean_dec(v_a_1100_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_del_object(v___x_1102_);
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1090_);
v___x_1106_ = l_Lean_indentExpr(v_e_1090_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_indentExpr(v_inst_1091_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1092_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1138_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1138_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1138_;
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
lean_dec_ref_known(v___x_1111_, 2);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_e_1090_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_e_1090_);
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
lean_object* v___x_1121_; 
lean_del_object(v___x_1115_);
v___x_1121_ = l_Lean_Meta_Sym_reportIssue(v___x_1111_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v_e_1090_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_e_1090_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_e_1090_);
v_a_1130_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref_known(v___x_1111_, 2);
lean_dec_ref(v_e_1090_);
v_a_1139_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1112_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1112_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v___x_1148_; 
lean_dec_ref(v_e_1090_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_inst_1091_);
v___x_1148_ = v___x_1102_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_inst_1091_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_inst_1091_);
lean_dec_ref(v_e_1090_);
v_a_1151_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1099_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1099_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1090_ = stack[0].m_obj;
lean_object* v_inst_1091_ = stack[1].m_obj;
lean_object* v_a_1092_ = stack[2].m_obj;
lean_object* v_a_1093_ = stack[3].m_obj;
lean_object* v_a_1094_ = stack[4].m_obj;
lean_object* v_a_1095_ = stack[5].m_obj;
lean_object* v_a_1096_ = stack[6].m_obj;
lean_object* v_a_1097_ = stack[7].m_obj;
lean_object* v_res_1159_;
v_res_1159_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1090_, v_inst_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1160_, lean_object* v_inst_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1160_, v_inst_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1173_, lean_object* v_type_1174_, uint8_t v_report_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
lean_inc_ref(v_type_1174_);
v___x_1183_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1174_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1235_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
if (lean_obj_tag(v_a_1184_) == 1)
{
lean_object* v_val_1188_; lean_object* v___x_1189_; 
lean_del_object(v___x_1186_);
lean_dec_ref(v_type_1174_);
v_val_1188_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v_a_1184_, 1);
v___x_1189_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1173_, v_val_1188_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1189_;
}
else
{
lean_dec(v_a_1184_);
if (v_report_1175_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_type_1174_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v_e_1173_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_e_1173_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1186_);
v___x_1193_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1173_);
v___x_1194_ = l_Lean_indentExpr(v_e_1173_);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_indentExpr(v_type_1174_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1176_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1226_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1226_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1226_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v_verbose_1205_; 
v_verbose_1205_ = lean_ctor_get_uint8(v_a_1201_, 0);
lean_dec(v_a_1201_);
if (v_verbose_1205_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref_known(v___x_1199_, 2);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v_e_1173_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_e_1173_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_object* v___x_1209_; 
lean_del_object(v___x_1203_);
v___x_1209_ = l_Lean_Meta_Sym_reportIssue(v___x_1199_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1209_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_e_1173_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_e_1173_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_e_1173_);
v_a_1218_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1209_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1209_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref_known(v___x_1199_, 2);
lean_dec_ref(v_e_1173_);
v_a_1227_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1200_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1200_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v_type_1174_);
lean_dec_ref(v_e_1173_);
v_a_1236_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1183_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1183_);
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1173_ = stack[0].m_obj;
lean_object* v_type_1174_ = stack[1].m_obj;
uint8_t v_report_1175_ = stack[2].m_num;
lean_object* v_a_1176_ = stack[3].m_obj;
lean_object* v_a_1177_ = stack[4].m_obj;
lean_object* v_a_1178_ = stack[5].m_obj;
lean_object* v_a_1179_ = stack[6].m_obj;
lean_object* v_a_1180_ = stack[7].m_obj;
lean_object* v_a_1181_ = stack[8].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1173_, v_type_1174_, v_report_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1245_, lean_object* v_type_1246_, lean_object* v_report_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
uint8_t v_report_boxed_1255_; lean_object* v_res_1256_; 
v_report_boxed_1255_ = lean_unbox(v_report_1247_);
v_res_1256_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1245_, v_type_1246_, v_report_boxed_1255_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1256_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1257_, lean_object* v_type_1258_, uint8_t v_report_1259_, uint8_t v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1257_, v_type_1258_, v_report_1259_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1257_ = stack[0].m_obj;
lean_object* v_type_1258_ = stack[1].m_obj;
uint8_t v_report_1259_ = stack[2].m_num;
uint8_t v_a_1260_ = stack[3].m_num;
lean_object* v_a_1261_ = stack[4].m_obj;
lean_object* v_a_1262_ = stack[5].m_obj;
lean_object* v_a_1263_ = stack[6].m_obj;
lean_object* v_a_1264_ = stack[7].m_obj;
lean_object* v_a_1265_ = stack[8].m_obj;
lean_object* v_a_1266_ = stack[9].m_obj;
lean_object* v_res_1269_;
v_res_1269_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1257_, v_type_1258_, v_report_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1270_, lean_object* v_type_1271_, lean_object* v_report_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v_report_boxed_1281_; uint8_t v_a_boxed_1282_; lean_object* v_res_1283_; 
v_report_boxed_1281_ = lean_unbox(v_report_1272_);
v_a_boxed_1282_ = lean_unbox(v_a_1273_);
v_res_1283_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1270_, v_type_1271_, v_report_boxed_1281_, v_a_boxed_1282_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
return v_res_1283_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
uint8_t v___x_1286_; 
v___x_1286_ = 0;
return v___x_1286_;
}
else
{
lean_object* v_key_1287_; lean_object* v_tail_1288_; uint8_t v___x_1289_; 
v_key_1287_ = lean_ctor_get(v_x_1285_, 0);
v_tail_1288_ = lean_ctor_get(v_x_1285_, 2);
v___x_1289_ = lean_expr_eqv(v_key_1287_, v_a_1284_);
if (v___x_1289_ == 0)
{
v_x_1285_ = v_tail_1288_;
goto _start;
}
else
{
return v___x_1289_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1284_ = stack[0].m_obj;
lean_object* v_x_1285_ = stack[1].m_obj;
uint8_t v_res_1291_;
v_res_1291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1284_, v_x_1285_);
stack->m_num = v_res_1291_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1292_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec_ref(v_a_1292_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
return v_x_1296_;
}
else
{
lean_object* v_key_1298_; lean_object* v_value_1299_; lean_object* v_tail_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1323_; 
v_key_1298_ = lean_ctor_get(v_x_1297_, 0);
v_value_1299_ = lean_ctor_get(v_x_1297_, 1);
v_tail_1300_ = lean_ctor_get(v_x_1297_, 2);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1302_ = v_x_1297_;
v_isShared_1303_ = v_isSharedCheck_1323_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_tail_1300_);
lean_inc(v_value_1299_);
lean_inc(v_key_1298_);
lean_dec(v_x_1297_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1323_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; uint64_t v___x_1305_; uint64_t v___x_1306_; uint64_t v___x_1307_; uint64_t v_fold_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1304_ = lean_array_get_size(v_x_1296_);
v___x_1305_ = l_Lean_Expr_hash(v_key_1298_);
v___x_1306_ = 32ULL;
v___x_1307_ = lean_uint64_shift_right(v___x_1305_, v___x_1306_);
v_fold_1308_ = lean_uint64_xor(v___x_1305_, v___x_1307_);
v___x_1309_ = 16ULL;
v___x_1310_ = lean_uint64_shift_right(v_fold_1308_, v___x_1309_);
v___x_1311_ = lean_uint64_xor(v_fold_1308_, v___x_1310_);
v___x_1312_ = lean_uint64_to_usize(v___x_1311_);
v___x_1313_ = lean_usize_of_nat(v___x_1304_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_sub(v___x_1313_, v___x_1314_);
v___x_1316_ = lean_usize_land(v___x_1312_, v___x_1315_);
v___x_1317_ = lean_array_uget_borrowed(v_x_1296_, v___x_1316_);
lean_inc(v___x_1317_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v___x_1317_);
v___x_1319_ = v___x_1302_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_key_1298_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_value_1299_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_array_uset(v_x_1296_, v___x_1316_, v___x_1319_);
v_x_1296_ = v___x_1320_;
v_x_1297_ = v_tail_1300_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object* v_i_1324_, lean_object* v_source_1325_, lean_object* v_target_1326_){
_start:
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_array_get_size(v_source_1325_);
v___x_1328_ = lean_nat_dec_lt(v_i_1324_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v_source_1325_);
lean_dec(v_i_1324_);
return v_target_1326_;
}
else
{
lean_object* v_es_1329_; lean_object* v___x_1330_; lean_object* v_source_1331_; lean_object* v_target_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_es_1329_ = lean_array_fget(v_source_1325_, v_i_1324_);
v___x_1330_ = lean_box(0);
v_source_1331_ = lean_array_fset(v_source_1325_, v_i_1324_, v___x_1330_);
v_target_1332_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_target_1326_, v_es_1329_);
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_nat_add(v_i_1324_, v___x_1333_);
lean_dec(v_i_1324_);
v_i_1324_ = v___x_1334_;
v_source_1325_ = v_source_1331_;
v_target_1326_ = v_target_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_nbuckets_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1337_ = lean_array_get_size(v_data_1336_);
v___x_1338_ = lean_unsigned_to_nat(2u);
v_nbuckets_1339_ = lean_nat_mul(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_mk_array(v_nbuckets_1339_, v___x_1341_);
v___x_1343_ = lean_array_propagate_mark(v_data_1336_, v___x_1342_);
v___x_1344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v___x_1340_, v_data_1336_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1345_, lean_object* v_b_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
lean_dec(v_b_1346_);
lean_dec_ref(v_a_1345_);
return v_x_1347_;
}
else
{
lean_object* v_key_1348_; lean_object* v_value_1349_; lean_object* v_tail_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v_key_1348_ = lean_ctor_get(v_x_1347_, 0);
v_value_1349_ = lean_ctor_get(v_x_1347_, 1);
v_tail_1350_ = lean_ctor_get(v_x_1347_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1347_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v_x_1347_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_tail_1350_);
lean_inc(v_value_1349_);
lean_inc(v_key_1348_);
lean_dec(v_x_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_expr_eqv(v_key_1348_, v_a_1345_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1345_, v_b_1346_, v_tail_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 2, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_key_1348_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_value_1349_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v___x_1360_; 
lean_dec(v_value_1349_);
lean_dec(v_key_1348_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v_b_1346_);
lean_ctor_set(v___x_1352_, 0, v_a_1345_);
v___x_1360_ = v___x_1352_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1345_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_b_1346_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_tail_1350_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1363_, lean_object* v_a_1364_, lean_object* v_b_1365_){
_start:
{
lean_object* v_size_1366_; lean_object* v_buckets_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1410_; 
v_size_1366_ = lean_ctor_get(v_m_1363_, 0);
v_buckets_1367_ = lean_ctor_get(v_m_1363_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_m_1363_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1369_ = v_m_1363_;
v_isShared_1370_ = v_isSharedCheck_1410_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_buckets_1367_);
lean_inc(v_size_1366_);
lean_dec(v_m_1363_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1410_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; uint64_t v_fold_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v_bkt_1384_; uint8_t v___x_1385_; 
v___x_1371_ = lean_array_get_size(v_buckets_1367_);
v___x_1372_ = l_Lean_Expr_hash(v_a_1364_);
v___x_1373_ = 32ULL;
v___x_1374_ = lean_uint64_shift_right(v___x_1372_, v___x_1373_);
v_fold_1375_ = lean_uint64_xor(v___x_1372_, v___x_1374_);
v___x_1376_ = 16ULL;
v___x_1377_ = lean_uint64_shift_right(v_fold_1375_, v___x_1376_);
v___x_1378_ = lean_uint64_xor(v_fold_1375_, v___x_1377_);
v___x_1379_ = lean_uint64_to_usize(v___x_1378_);
v___x_1380_ = lean_usize_of_nat(v___x_1371_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_sub(v___x_1380_, v___x_1381_);
v___x_1383_ = lean_usize_land(v___x_1379_, v___x_1382_);
v_bkt_1384_ = lean_array_uget_borrowed(v_buckets_1367_, v___x_1383_);
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1364_, v_bkt_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_size_x27_1387_; lean_object* v___x_1388_; lean_object* v_buckets_x27_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
v_size_x27_1387_ = lean_nat_add(v_size_1366_, v___x_1386_);
lean_dec(v_size_1366_);
lean_inc(v_bkt_1384_);
v___x_1388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1364_);
lean_ctor_set(v___x_1388_, 1, v_b_1365_);
lean_ctor_set(v___x_1388_, 2, v_bkt_1384_);
v_buckets_x27_1389_ = lean_array_uset(v_buckets_1367_, v___x_1383_, v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(4u);
v___x_1391_ = lean_nat_mul(v_size_x27_1387_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(3u);
v___x_1393_ = lean_nat_div(v___x_1391_, v___x_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_array_get_size(v_buckets_x27_1389_);
v___x_1395_ = lean_nat_dec_le(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
if (v___x_1395_ == 0)
{
lean_object* v_val_1396_; lean_object* v___x_1398_; 
v_val_1396_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1389_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_val_1396_);
lean_ctor_set(v___x_1369_, 0, v_size_x27_1387_);
v___x_1398_ = v___x_1369_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_size_x27_1387_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_val_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v___x_1401_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_buckets_x27_1389_);
lean_ctor_set(v___x_1369_, 0, v_size_x27_1387_);
v___x_1401_ = v___x_1369_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_size_x27_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_buckets_x27_1389_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v___x_1403_; lean_object* v_buckets_x27_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_inc(v_bkt_1384_);
v___x_1403_ = lean_box(0);
v_buckets_x27_1404_ = lean_array_uset(v_buckets_1367_, v___x_1383_, v___x_1403_);
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1364_, v_b_1365_, v_bkt_1384_);
v___x_1406_ = lean_array_uset(v_buckets_x27_1404_, v___x_1383_, v___x_1405_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1406_);
v___x_1408_ = v___x_1369_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_size_1366_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object* v_k_1411_, uint8_t v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(v___y_1412_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
v___x_1422_ = lean_apply_9(v_k_1411_, v_b_1415_, v___x_1421_, v___y_1413_, v___y_1414_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
return v___x_1422_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1411_ = stack[0].m_obj;
uint8_t v___y_1412_ = stack[1].m_num;
lean_object* v___y_1413_ = stack[2].m_obj;
lean_object* v___y_1414_ = stack[3].m_obj;
lean_object* v_b_1415_ = stack[4].m_obj;
lean_object* v___y_1416_ = stack[5].m_obj;
lean_object* v___y_1417_ = stack[6].m_obj;
lean_object* v___y_1418_ = stack[7].m_obj;
lean_object* v___y_1419_ = stack[8].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object* v_k_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v___y_61899__boxed_1434_; lean_object* v_res_1435_; 
v___y_61899__boxed_1434_ = lean_unbox(v___y_1425_);
v_res_1435_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1424_, v___y_61899__boxed_1434_, v___y_1426_, v___y_1427_, v_b_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1435_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object* v_name_1436_, uint8_t v_bi_1437_, lean_object* v_type_1438_, lean_object* v_k_1439_, uint8_t v_kind_1440_, uint8_t v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_box(v___y_1441_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___f_1450_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1450_, 0, v_k_1439_);
lean_closure_set(v___f_1450_, 1, v___x_1449_);
lean_closure_set(v___f_1450_, 2, v___y_1442_);
lean_closure_set(v___f_1450_, 3, v___y_1443_);
v___x_1451_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1436_, v_bi_1437_, v_type_1438_, v___f_1450_, v_kind_1440_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
return v___x_1451_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1436_ = stack[0].m_obj;
uint8_t v_bi_1437_ = stack[1].m_num;
lean_object* v_type_1438_ = stack[2].m_obj;
lean_object* v_k_1439_ = stack[3].m_obj;
uint8_t v_kind_1440_ = stack[4].m_num;
uint8_t v___y_1441_ = stack[5].m_num;
lean_object* v___y_1442_ = stack[6].m_obj;
lean_object* v___y_1443_ = stack[7].m_obj;
lean_object* v___y_1444_ = stack[8].m_obj;
lean_object* v___y_1445_ = stack[9].m_obj;
lean_object* v___y_1446_ = stack[10].m_obj;
lean_object* v___y_1447_ = stack[11].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1436_, v_bi_1437_, v_type_1438_, v_k_1439_, v_kind_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1460_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object* v_name_1461_, lean_object* v_bi_1462_, lean_object* v_type_1463_, lean_object* v_k_1464_, lean_object* v_kind_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_bi_boxed_1474_; uint8_t v_kind_boxed_1475_; uint8_t v___y_61945__boxed_1476_; lean_object* v_res_1477_; 
v_bi_boxed_1474_ = lean_unbox(v_bi_1462_);
v_kind_boxed_1475_ = lean_unbox(v_kind_1465_);
v___y_61945__boxed_1476_ = lean_unbox(v___y_1466_);
v_res_1477_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1461_, v_bi_boxed_1474_, v_type_1463_, v_k_1464_, v_kind_boxed_1475_, v___y_61945__boxed_1476_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1477_;
}
}
lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v_env_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1481_ = lean_st_ref_get(v___y_1479_);
v_env_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_env_1482_);
lean_dec(v___x_1481_);
v___x_1483_ = l_Lean_Meta_isMatcherCore(v_env_1482_, v_declName_1478_);
v___x_1484_ = lean_box(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1478_ = stack[0].m_obj;
lean_object* v___y_1479_ = stack[1].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1478_, v___y_1479_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1487_, v___y_1488_);
lean_dec(v___y_1488_);
return v_res_1490_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v_env_1498_; uint8_t v___x_1499_; lean_object* v_env_1500_; lean_object* v___x_1501_; lean_object* v_toCold_1502_; lean_object* v_mctx_1503_; lean_object* v_lctx_1504_; lean_object* v_options_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1497_ = lean_st_ref_get(v___y_1495_);
v_env_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_env_1498_);
lean_dec(v___x_1497_);
v___x_1499_ = 0;
v_env_1500_ = l_Lean_Environment_setRecordingDeps(v_env_1498_, v___x_1499_);
v___x_1501_ = lean_st_ref_get(v___y_1493_);
v_toCold_1502_ = lean_ctor_get(v___y_1494_, 0);
v_mctx_1503_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_mctx_1503_);
lean_dec(v___x_1501_);
v_lctx_1504_ = lean_ctor_get(v___y_1492_, 2);
v_options_1505_ = lean_ctor_get(v_toCold_1502_, 2);
lean_inc_ref(v_options_1505_);
lean_inc_ref(v_lctx_1504_);
v___x_1506_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1506_, 0, v_env_1500_);
lean_ctor_set(v___x_1506_, 1, v_mctx_1503_);
lean_ctor_set(v___x_1506_, 2, v_lctx_1504_);
lean_ctor_set(v___x_1506_, 3, v_options_1505_);
v___x_1507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_msgData_1491_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1491_ = stack[0].m_obj;
lean_object* v___y_1492_ = stack[1].m_obj;
lean_object* v___y_1493_ = stack[2].m_obj;
lean_object* v___y_1494_ = stack[3].m_obj;
lean_object* v___y_1495_ = stack[4].m_obj;
lean_object* v_res_1509_;
v_res_1509_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
stack->m_obj
 = v_res_1509_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1516_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1517_; double v___x_1518_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_float_of_nat(v___x_1517_);
return v___x_1518_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_ref_1529_; lean_object* v___x_1530_; lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1576_; 
v_ref_1529_ = lean_ctor_get(v___y_1526_, 2);
v___x_1530_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1576_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1576_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v_traceState_1536_; lean_object* v_env_1537_; lean_object* v_nextMacroScope_1538_; lean_object* v_ngen_1539_; lean_object* v_auxDeclNGen_1540_; lean_object* v_cache_1541_; lean_object* v_recordedDeps_1542_; lean_object* v_messages_1543_; lean_object* v_infoState_1544_; lean_object* v_snapshotTasks_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1575_; 
v___x_1535_ = lean_st_ref_take(v___y_1527_);
v_traceState_1536_ = lean_ctor_get(v___x_1535_, 4);
v_env_1537_ = lean_ctor_get(v___x_1535_, 0);
v_nextMacroScope_1538_ = lean_ctor_get(v___x_1535_, 1);
v_ngen_1539_ = lean_ctor_get(v___x_1535_, 2);
v_auxDeclNGen_1540_ = lean_ctor_get(v___x_1535_, 3);
v_cache_1541_ = lean_ctor_get(v___x_1535_, 5);
v_recordedDeps_1542_ = lean_ctor_get(v___x_1535_, 6);
v_messages_1543_ = lean_ctor_get(v___x_1535_, 7);
v_infoState_1544_ = lean_ctor_get(v___x_1535_, 8);
v_snapshotTasks_1545_ = lean_ctor_get(v___x_1535_, 9);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1547_ = v___x_1535_;
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snapshotTasks_1545_);
lean_inc(v_infoState_1544_);
lean_inc(v_messages_1543_);
lean_inc(v_recordedDeps_1542_);
lean_inc(v_cache_1541_);
lean_inc(v_traceState_1536_);
lean_inc(v_auxDeclNGen_1540_);
lean_inc(v_ngen_1539_);
lean_inc(v_nextMacroScope_1538_);
lean_inc(v_env_1537_);
lean_dec(v___x_1535_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint64_t v_tid_1549_; lean_object* v_traces_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1574_; 
v_tid_1549_ = lean_ctor_get_uint64(v_traceState_1536_, sizeof(void*)*1);
v_traces_1550_ = lean_ctor_get(v_traceState_1536_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_traceState_1536_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1552_ = v_traceState_1536_;
v_isShared_1553_ = v_isSharedCheck_1574_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_traces_1550_);
lean_dec(v_traceState_1536_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1574_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; double v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1557_ = 0;
v___x_1558_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1559_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1559_, 0, v_cls_1522_);
lean_ctor_set(v___x_1559_, 1, v___x_1555_);
lean_ctor_set(v___x_1559_, 2, v___x_1558_);
lean_ctor_set_float(v___x_1559_, sizeof(void*)*3, v___x_1556_);
lean_ctor_set_float(v___x_1559_, sizeof(void*)*3 + 8, v___x_1556_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*3 + 16, v___x_1557_);
v___x_1560_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1561_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v_a_1531_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
lean_inc(v_ref_1529_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_ref_1529_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_PersistentArray_push___redArg(v_traces_1550_, v___x_1562_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1563_);
v___x_1565_ = v___x_1552_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1563_);
lean_ctor_set_uint64(v_reuseFailAlloc_1573_, sizeof(void*)*1, v_tid_1549_);
v___x_1565_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v___x_1565_);
v___x_1567_ = v___x_1547_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_env_1537_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_nextMacroScope_1538_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_ngen_1539_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_auxDeclNGen_1540_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v_cache_1541_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v_recordedDeps_1542_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v_messages_1543_);
lean_ctor_set(v_reuseFailAlloc_1572_, 8, v_infoState_1544_);
lean_ctor_set(v_reuseFailAlloc_1572_, 9, v_snapshotTasks_1545_);
v___x_1567_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_st_ref_put(v___y_1527_, v___x_1567_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1554_);
v___x_1570_ = v___x_1533_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1554_);
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
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1522_ = stack[0].m_obj;
lean_object* v_msg_1523_ = stack[1].m_obj;
lean_object* v___y_1524_ = stack[2].m_obj;
lean_object* v___y_1525_ = stack[3].m_obj;
lean_object* v___y_1526_ = stack[4].m_obj;
lean_object* v___y_1527_ = stack[5].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1522_, v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1578_, lean_object* v_msg_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1578_, v_msg_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
else
{
lean_object* v_key_1589_; lean_object* v_value_1590_; lean_object* v_tail_1591_; uint8_t v___x_1592_; 
v_key_1589_ = lean_ctor_get(v_x_1587_, 0);
v_value_1590_ = lean_ctor_get(v_x_1587_, 1);
v_tail_1591_ = lean_ctor_get(v_x_1587_, 2);
v___x_1592_ = lean_expr_eqv(v_key_1589_, v_a_1586_);
if (v___x_1592_ == 0)
{
v_x_1587_ = v_tail_1591_;
goto _start;
}
else
{
lean_object* v___x_1594_; 
lean_inc(v_value_1590_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_value_1590_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1595_, v_x_1596_);
lean_dec(v_x_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_buckets_1600_; lean_object* v___x_1601_; uint64_t v___x_1602_; uint64_t v___x_1603_; uint64_t v___x_1604_; uint64_t v_fold_1605_; uint64_t v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_buckets_1600_ = lean_ctor_get(v_m_1598_, 1);
v___x_1601_ = lean_array_get_size(v_buckets_1600_);
v___x_1602_ = l_Lean_Expr_hash(v_a_1599_);
v___x_1603_ = 32ULL;
v___x_1604_ = lean_uint64_shift_right(v___x_1602_, v___x_1603_);
v_fold_1605_ = lean_uint64_xor(v___x_1602_, v___x_1604_);
v___x_1606_ = 16ULL;
v___x_1607_ = lean_uint64_shift_right(v_fold_1605_, v___x_1606_);
v___x_1608_ = lean_uint64_xor(v_fold_1605_, v___x_1607_);
v___x_1609_ = lean_uint64_to_usize(v___x_1608_);
v___x_1610_ = lean_usize_of_nat(v___x_1601_);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_sub(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_usize_land(v___x_1609_, v___x_1612_);
v___x_1614_ = lean_array_uget_borrowed(v_buckets_1600_, v___x_1613_);
v___x_1615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1599_, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_m_1616_);
return v_res_1618_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; lean_object* v_env_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = lean_st_ref_get(v___y_1620_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1623_, v_declName_1619_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1619_ = stack[0].m_obj;
lean_object* v___y_1620_ = stack[1].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1619_, v___y_1620_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1627_, v___y_1628_);
lean_dec(v___y_1628_);
return v_res_1630_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object* v_name_1631_, lean_object* v_type_1632_, lean_object* v_val_1633_, lean_object* v_k_1634_, uint8_t v_nondep_1635_, uint8_t v_kind_1636_, uint8_t v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_box(v___y_1637_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1646_, 0, v_k_1634_);
lean_closure_set(v___f_1646_, 1, v___x_1645_);
lean_closure_set(v___f_1646_, 2, v___y_1638_);
lean_closure_set(v___f_1646_, 3, v___y_1639_);
v___x_1647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1631_, v_type_1632_, v_val_1633_, v___f_1646_, v_nondep_1635_, v_kind_1636_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1647_) == 0)
{
return v___x_1647_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1631_ = stack[0].m_obj;
lean_object* v_type_1632_ = stack[1].m_obj;
lean_object* v_val_1633_ = stack[2].m_obj;
lean_object* v_k_1634_ = stack[3].m_obj;
uint8_t v_nondep_1635_ = stack[4].m_num;
uint8_t v_kind_1636_ = stack[5].m_num;
uint8_t v___y_1637_ = stack[6].m_num;
lean_object* v___y_1638_ = stack[7].m_obj;
lean_object* v___y_1639_ = stack[8].m_obj;
lean_object* v___y_1640_ = stack[9].m_obj;
lean_object* v___y_1641_ = stack[10].m_obj;
lean_object* v___y_1642_ = stack[11].m_obj;
lean_object* v___y_1643_ = stack[12].m_obj;
lean_object* v_res_1656_;
v_res_1656_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1631_, v_type_1632_, v_val_1633_, v_k_1634_, v_nondep_1635_, v_kind_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
stack->m_obj
 = v_res_1656_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object* v_name_1657_, lean_object* v_type_1658_, lean_object* v_val_1659_, lean_object* v_k_1660_, lean_object* v_nondep_1661_, lean_object* v_kind_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v_nondep_boxed_1671_; uint8_t v_kind_boxed_1672_; uint8_t v___y_62326__boxed_1673_; lean_object* v_res_1674_; 
v_nondep_boxed_1671_ = lean_unbox(v_nondep_1661_);
v_kind_boxed_1672_ = lean_unbox(v_kind_1662_);
v___y_62326__boxed_1673_ = lean_unbox(v___y_1663_);
v_res_1674_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1657_, v_type_1658_, v_val_1659_, v_k_1660_, v_nondep_boxed_1671_, v_kind_boxed_1672_, v___y_62326__boxed_1673_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l_Lean_instInhabitedExpr;
v___x_1677_ = lean_panic_fn_borrowed(v___x_1676_, v_msg_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1678_, lean_object* v_body_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v___y_62528__boxed_1689_; lean_object* v_res_1690_; 
v___y_62528__boxed_1689_ = lean_unbox(v___y_1681_);
v_res_1690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1678_, v_body_1679_, v_x_1680_, v___y_62528__boxed_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1690_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1693_, lean_object* v_body_1694_, lean_object* v_x_1695_, uint8_t v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_array_push(v_fvars_1693_, v_x_1695_);
v___x_1705_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1704_, v_body_1694_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1705_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1693_ = stack[0].m_obj;
lean_object* v_body_1694_ = stack[1].m_obj;
lean_object* v_x_1695_ = stack[2].m_obj;
uint8_t v___y_1696_ = stack[3].m_num;
lean_object* v___y_1697_ = stack[4].m_obj;
lean_object* v___y_1698_ = stack[5].m_obj;
lean_object* v___y_1699_ = stack[6].m_obj;
lean_object* v___y_1700_ = stack[7].m_obj;
lean_object* v___y_1701_ = stack[8].m_obj;
lean_object* v___y_1702_ = stack[9].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1693_, v_body_1694_, v_x_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1707_, lean_object* v_body_1708_, lean_object* v_x_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___y_62539__boxed_1718_; lean_object* v_res_1719_; 
v___y_62539__boxed_1718_ = lean_unbox(v___y_1710_);
v_res_1719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1707_, v_body_1708_, v_x_1709_, v___y_62539__boxed_1718_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1719_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1720_, lean_object* v_e_1721_, uint8_t v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
if (lean_obj_tag(v_e_1721_) == 6)
{
lean_object* v_binderName_1730_; lean_object* v_binderType_1731_; lean_object* v_body_1732_; uint8_t v_binderInfo_1733_; lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_binderName_1730_ = lean_ctor_get(v_e_1721_, 0);
lean_inc(v_binderName_1730_);
v_binderType_1731_ = lean_ctor_get(v_e_1721_, 1);
lean_inc_ref(v_binderType_1731_);
v_body_1732_ = lean_ctor_get(v_e_1721_, 2);
lean_inc_ref(v_body_1732_);
v_binderInfo_1733_ = lean_ctor_get_uint8(v_e_1721_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1721_, 3);
lean_inc_ref(v_fvars_1720_);
v___f_1734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1734_, 0, v_fvars_1720_);
lean_closure_set(v___f_1734_, 1, v_body_1732_);
v___x_1735_ = lean_expr_instantiate_rev(v_binderType_1731_, v_fvars_1720_);
lean_dec_ref(v_fvars_1720_);
lean_dec_ref(v_binderType_1731_);
v___x_1736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1735_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = 0;
v___x_1739_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_1730_, v_binderInfo_1733_, v_a_1737_, v___f_1734_, v___x_1738_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
return v___x_1739_;
}
else
{
lean_dec_ref(v___f_1734_);
lean_dec(v_binderName_1730_);
return v___x_1736_;
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_expr_instantiate_rev(v_e_1721_, v_fvars_1720_);
lean_dec_ref(v_e_1721_);
v___x_1741_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1740_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = 0;
v___x_1744_ = 1;
v___x_1745_ = 1;
v___x_1746_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1720_, v_a_1742_, v___x_1743_, v___x_1744_, v___x_1743_, v___x_1744_, v___x_1745_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_fvars_1720_);
return v___x_1746_;
}
else
{
lean_dec_ref(v_fvars_1720_);
return v___x_1741_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1720_ = stack[0].m_obj;
lean_object* v_e_1721_ = stack[1].m_obj;
uint8_t v_a_1722_ = stack[2].m_num;
lean_object* v_a_1723_ = stack[3].m_obj;
lean_object* v_a_1724_ = stack[4].m_obj;
lean_object* v_a_1725_ = stack[5].m_obj;
lean_object* v_a_1726_ = stack[6].m_obj;
lean_object* v_a_1727_ = stack[7].m_obj;
lean_object* v_a_1728_ = stack[8].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_1720_, v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
stack->m_obj
 = v_res_1747_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1748_, uint8_t v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
if (v_a_1749_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1758_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1757_, v_e_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1760_ = l_Lean_Meta_Sym_etaReduce(v_e_1748_);
lean_dec_ref(v_e_1748_);
v___x_1761_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1759_, v___x_1760_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1761_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1748_ = stack[0].m_obj;
uint8_t v_a_1749_ = stack[1].m_num;
lean_object* v_a_1750_ = stack[2].m_obj;
lean_object* v_a_1751_ = stack[3].m_obj;
lean_object* v_a_1752_ = stack[4].m_obj;
lean_object* v_a_1753_ = stack[5].m_obj;
lean_object* v_a_1754_ = stack[6].m_obj;
lean_object* v_a_1755_ = stack[7].m_obj;
lean_object* v_res_1762_;
v_res_1762_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
stack->m_obj
 = v_res_1762_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1763_, lean_object* v_body_1764_, lean_object* v_x_1765_, uint8_t v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_array_push(v_fvars_1763_, v_x_1765_);
v___x_1775_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1774_, v_body_1764_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1775_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1763_ = stack[0].m_obj;
lean_object* v_body_1764_ = stack[1].m_obj;
lean_object* v_x_1765_ = stack[2].m_obj;
uint8_t v___y_1766_ = stack[3].m_num;
lean_object* v___y_1767_ = stack[4].m_obj;
lean_object* v___y_1768_ = stack[5].m_obj;
lean_object* v___y_1769_ = stack[6].m_obj;
lean_object* v___y_1770_ = stack[7].m_obj;
lean_object* v___y_1771_ = stack[8].m_obj;
lean_object* v___y_1772_ = stack[9].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1763_, v_body_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1777_, lean_object* v_body_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v___y_62550__boxed_1788_; lean_object* v_res_1789_; 
v___y_62550__boxed_1788_ = lean_unbox(v___y_1780_);
v_res_1789_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1777_, v_body_1778_, v_x_1779_, v___y_62550__boxed_1788_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1789_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1790_, lean_object* v_e_1791_, uint8_t v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
if (lean_obj_tag(v_e_1791_) == 8)
{
lean_object* v_declName_1800_; lean_object* v_type_1801_; lean_object* v_value_1802_; lean_object* v_body_1803_; uint8_t v_nondep_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_declName_1800_ = lean_ctor_get(v_e_1791_, 0);
lean_inc(v_declName_1800_);
v_type_1801_ = lean_ctor_get(v_e_1791_, 1);
lean_inc_ref(v_type_1801_);
v_value_1802_ = lean_ctor_get(v_e_1791_, 2);
lean_inc_ref(v_value_1802_);
v_body_1803_ = lean_ctor_get(v_e_1791_, 3);
lean_inc_ref(v_body_1803_);
v_nondep_1804_ = lean_ctor_get_uint8(v_e_1791_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1791_, 4);
lean_inc_ref(v_fvars_1790_);
v___f_1805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1805_, 0, v_fvars_1790_);
lean_closure_set(v___f_1805_, 1, v_body_1803_);
v___x_1806_ = lean_expr_instantiate_rev(v_type_1801_, v_fvars_1790_);
lean_dec_ref(v_type_1801_);
v___x_1807_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1806_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = lean_expr_instantiate_rev(v_value_1802_, v_fvars_1790_);
lean_dec_ref(v_fvars_1790_);
lean_dec_ref(v_value_1802_);
v___x_1810_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1809_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = 0;
v___x_1813_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_declName_1800_, v_a_1808_, v_a_1811_, v___f_1805_, v_nondep_1804_, v___x_1812_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1813_;
}
else
{
lean_dec(v_a_1808_);
lean_dec_ref(v___f_1805_);
lean_dec(v_declName_1800_);
return v___x_1810_;
}
}
else
{
lean_dec_ref(v___f_1805_);
lean_dec_ref(v_value_1802_);
lean_dec(v_declName_1800_);
lean_dec_ref(v_fvars_1790_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_expr_instantiate_rev(v_e_1791_, v_fvars_1790_);
lean_dec_ref(v_e_1791_);
v___x_1815_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1814_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; uint8_t v___x_1817_; uint8_t v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v___x_1817_ = 1;
v___x_1818_ = 0;
v___x_1819_ = 1;
v___x_1820_ = l_Lean_Meta_mkLetFVars(v_fvars_1790_, v_a_1816_, v___x_1817_, v___x_1818_, v___x_1819_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec_ref(v_fvars_1790_);
return v___x_1820_;
}
else
{
lean_dec_ref(v_fvars_1790_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1790_ = stack[0].m_obj;
lean_object* v_e_1791_ = stack[1].m_obj;
uint8_t v_a_1792_ = stack[2].m_num;
lean_object* v_a_1793_ = stack[3].m_obj;
lean_object* v_a_1794_ = stack[4].m_obj;
lean_object* v_a_1795_ = stack[5].m_obj;
lean_object* v_a_1796_ = stack[6].m_obj;
lean_object* v_a_1797_ = stack[7].m_obj;
lean_object* v_a_1798_ = stack[8].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_1790_, v_e_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
stack->m_obj
 = v_res_1821_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1822_, uint8_t v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
if (v_a_1823_ == 0)
{
uint8_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = 1;
v___x_1832_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1822_, v___x_1831_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1833_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1822_ = stack[0].m_obj;
uint8_t v_a_1823_ = stack[1].m_num;
lean_object* v_a_1824_ = stack[2].m_obj;
lean_object* v_a_1825_ = stack[3].m_obj;
lean_object* v_a_1826_ = stack[4].m_obj;
lean_object* v_a_1827_ = stack[5].m_obj;
lean_object* v_a_1828_ = stack[6].m_obj;
lean_object* v_a_1829_ = stack[7].m_obj;
lean_object* v_res_1834_;
v_res_1834_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
stack->m_obj
 = v_res_1834_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1835_, uint8_t v_report_1836_, uint8_t v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1845_; 
lean_inc(v_a_1843_);
lean_inc_ref(v_a_1842_);
lean_inc(v_a_1841_);
lean_inc_ref(v_a_1840_);
lean_inc_ref(v_e_1835_);
v___x_1845_ = lean_infer_type(v_e_1835_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_n(v_a_1846_, 2);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l_Lean_Meta_isProp(v_a_1846_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1860_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
if (v_a_1837_ == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_unbox(v_a_1848_);
lean_dec(v_a_1848_);
if (v___x_1856_ == 0)
{
lean_del_object(v___x_1850_);
goto v___jp_1852_;
}
else
{
lean_object* v___x_1858_; 
lean_dec(v_a_1846_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_e_1835_);
v___x_1858_ = v___x_1850_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_e_1835_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_del_object(v___x_1850_);
lean_dec(v_a_1848_);
goto v___jp_1852_;
}
v___jp_1852_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1846_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1835_, v_a_1854_, v_report_1836_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1855_;
}
else
{
lean_dec_ref(v_e_1835_);
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1846_);
lean_dec_ref(v_e_1835_);
v_a_1861_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1847_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1847_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_dec_ref(v_e_1835_);
return v___x_1845_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1835_ = stack[0].m_obj;
uint8_t v_report_1836_ = stack[1].m_num;
uint8_t v_a_1837_ = stack[2].m_num;
lean_object* v_a_1838_ = stack[3].m_obj;
lean_object* v_a_1839_ = stack[4].m_obj;
lean_object* v_a_1840_ = stack[5].m_obj;
lean_object* v_a_1841_ = stack[6].m_obj;
lean_object* v_a_1842_ = stack[7].m_obj;
lean_object* v_a_1843_ = stack[8].m_obj;
lean_object* v_res_1869_;
v_res_1869_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1835_, v_report_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
stack->m_obj
 = v_res_1869_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1870_, uint8_t v_report_1871_, uint8_t v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
if (v_a_1872_ == 0)
{
lean_object* v___x_1880_; lean_object* v_canon_1881_; lean_object* v_cache_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_st_ref_get(v_a_1874_);
v_canon_1881_ = lean_ctor_get(v___x_1880_, 10);
lean_inc_ref(v_canon_1881_);
lean_dec(v___x_1880_);
v_cache_1882_ = lean_ctor_get(v_canon_1881_, 0);
lean_inc_ref(v_cache_1882_);
lean_dec_ref(v_canon_1881_);
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1882_, v_e_1870_);
lean_dec_ref(v_cache_1882_);
if (lean_obj_tag(v___x_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_e_1870_);
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 0);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_val_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v___x_1883_);
lean_inc_ref(v_e_1870_);
v___x_1892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1870_, v_report_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1932_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1932_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1932_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v_canon_1898_; lean_object* v_share_1899_; lean_object* v_maxFVar_1900_; lean_object* v_proofInstInfo_1901_; lean_object* v_proofInstInfoFVar_1902_; lean_object* v_inferType_1903_; lean_object* v_getLevel_1904_; lean_object* v_congrInfo_1905_; lean_object* v_defEqI_1906_; lean_object* v_extensions_1907_; lean_object* v_issues_1908_; lean_object* v_instanceOverrides_1909_; uint8_t v_debug_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1931_; 
v___x_1897_ = lean_st_ref_take(v_a_1874_);
v_canon_1898_ = lean_ctor_get(v___x_1897_, 10);
v_share_1899_ = lean_ctor_get(v___x_1897_, 0);
v_maxFVar_1900_ = lean_ctor_get(v___x_1897_, 1);
v_proofInstInfo_1901_ = lean_ctor_get(v___x_1897_, 2);
v_proofInstInfoFVar_1902_ = lean_ctor_get(v___x_1897_, 3);
v_inferType_1903_ = lean_ctor_get(v___x_1897_, 4);
v_getLevel_1904_ = lean_ctor_get(v___x_1897_, 5);
v_congrInfo_1905_ = lean_ctor_get(v___x_1897_, 6);
v_defEqI_1906_ = lean_ctor_get(v___x_1897_, 7);
v_extensions_1907_ = lean_ctor_get(v___x_1897_, 8);
v_issues_1908_ = lean_ctor_get(v___x_1897_, 9);
v_instanceOverrides_1909_ = lean_ctor_get(v___x_1897_, 11);
v_debug_1910_ = lean_ctor_get_uint8(v___x_1897_, sizeof(void*)*12);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1912_ = v___x_1897_;
v_isShared_1913_ = v_isSharedCheck_1931_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_instanceOverrides_1909_);
lean_inc(v_canon_1898_);
lean_inc(v_issues_1908_);
lean_inc(v_extensions_1907_);
lean_inc(v_defEqI_1906_);
lean_inc(v_congrInfo_1905_);
lean_inc(v_getLevel_1904_);
lean_inc(v_inferType_1903_);
lean_inc(v_proofInstInfoFVar_1902_);
lean_inc(v_proofInstInfo_1901_);
lean_inc(v_maxFVar_1900_);
lean_inc(v_share_1899_);
lean_dec(v___x_1897_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1931_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_cache_1914_; lean_object* v_cacheInType_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1930_; 
v_cache_1914_ = lean_ctor_get(v_canon_1898_, 0);
v_cacheInType_1915_ = lean_ctor_get(v_canon_1898_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_canon_1898_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1917_ = v_canon_1898_;
v_isShared_1918_ = v_isSharedCheck_1930_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_cacheInType_1915_);
lean_inc(v_cache_1914_);
lean_dec(v_canon_1898_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1930_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_inc(v_a_1893_);
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1914_, v_e_1870_, v_a_1893_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1919_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_cacheInType_1915_);
v___x_1921_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 10, v___x_1921_);
v___x_1923_ = v___x_1912_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_share_1899_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_maxFVar_1900_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_proofInstInfo_1901_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_proofInstInfoFVar_1902_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_inferType_1903_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_getLevel_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_congrInfo_1905_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_defEqI_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v_extensions_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_issues_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_instanceOverrides_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*12, v_debug_1910_);
v___x_1923_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_st_ref_put(v_a_1874_, v___x_1923_);
if (v_isShared_1896_ == 0)
{
v___x_1926_ = v___x_1895_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1893_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1870_);
return v___x_1892_;
}
}
}
else
{
lean_object* v___x_1933_; lean_object* v_canon_1934_; lean_object* v_cacheInType_1935_; lean_object* v___x_1936_; 
v___x_1933_ = lean_st_ref_get(v_a_1874_);
v_canon_1934_ = lean_ctor_get(v___x_1933_, 10);
lean_inc_ref(v_canon_1934_);
lean_dec(v___x_1933_);
v_cacheInType_1935_ = lean_ctor_get(v_canon_1934_, 1);
lean_inc_ref(v_cacheInType_1935_);
lean_dec_ref(v_canon_1934_);
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1935_, v_e_1870_);
lean_dec_ref(v_cacheInType_1935_);
if (lean_obj_tag(v___x_1936_) == 1)
{
lean_object* v_val_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_e_1870_);
v_val_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_val_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 0);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_val_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v___x_1945_; 
lean_dec(v___x_1936_);
lean_inc_ref(v_e_1870_);
v___x_1945_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1870_, v_report_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1985_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1985_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1985_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v_canon_1951_; lean_object* v_share_1952_; lean_object* v_maxFVar_1953_; lean_object* v_proofInstInfo_1954_; lean_object* v_proofInstInfoFVar_1955_; lean_object* v_inferType_1956_; lean_object* v_getLevel_1957_; lean_object* v_congrInfo_1958_; lean_object* v_defEqI_1959_; lean_object* v_extensions_1960_; lean_object* v_issues_1961_; lean_object* v_instanceOverrides_1962_; uint8_t v_debug_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1984_; 
v___x_1950_ = lean_st_ref_take(v_a_1874_);
v_canon_1951_ = lean_ctor_get(v___x_1950_, 10);
v_share_1952_ = lean_ctor_get(v___x_1950_, 0);
v_maxFVar_1953_ = lean_ctor_get(v___x_1950_, 1);
v_proofInstInfo_1954_ = lean_ctor_get(v___x_1950_, 2);
v_proofInstInfoFVar_1955_ = lean_ctor_get(v___x_1950_, 3);
v_inferType_1956_ = lean_ctor_get(v___x_1950_, 4);
v_getLevel_1957_ = lean_ctor_get(v___x_1950_, 5);
v_congrInfo_1958_ = lean_ctor_get(v___x_1950_, 6);
v_defEqI_1959_ = lean_ctor_get(v___x_1950_, 7);
v_extensions_1960_ = lean_ctor_get(v___x_1950_, 8);
v_issues_1961_ = lean_ctor_get(v___x_1950_, 9);
v_instanceOverrides_1962_ = lean_ctor_get(v___x_1950_, 11);
v_debug_1963_ = lean_ctor_get_uint8(v___x_1950_, sizeof(void*)*12);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1965_ = v___x_1950_;
v_isShared_1966_ = v_isSharedCheck_1984_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_instanceOverrides_1962_);
lean_inc(v_canon_1951_);
lean_inc(v_issues_1961_);
lean_inc(v_extensions_1960_);
lean_inc(v_defEqI_1959_);
lean_inc(v_congrInfo_1958_);
lean_inc(v_getLevel_1957_);
lean_inc(v_inferType_1956_);
lean_inc(v_proofInstInfoFVar_1955_);
lean_inc(v_proofInstInfo_1954_);
lean_inc(v_maxFVar_1953_);
lean_inc(v_share_1952_);
lean_dec(v___x_1950_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1984_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_cache_1967_; lean_object* v_cacheInType_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1983_; 
v_cache_1967_ = lean_ctor_get(v_canon_1951_, 0);
v_cacheInType_1968_ = lean_ctor_get(v_canon_1951_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_canon_1951_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1970_ = v_canon_1951_;
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_cacheInType_1968_);
lean_inc(v_cache_1967_);
lean_dec(v_canon_1951_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_inc(v_a_1946_);
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1968_, v_e_1870_, v_a_1946_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_cache_1967_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 10, v___x_1974_);
v___x_1976_ = v___x_1965_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_share_1952_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_maxFVar_1953_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_proofInstInfo_1954_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_proofInstInfoFVar_1955_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_inferType_1956_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_getLevel_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_congrInfo_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_defEqI_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_extensions_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_issues_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 10, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1981_, 11, v_instanceOverrides_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*12, v_debug_1963_);
v___x_1976_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_st_ref_put(v_a_1874_, v___x_1976_);
if (v_isShared_1949_ == 0)
{
v___x_1979_ = v___x_1948_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1946_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1870_);
return v___x_1945_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1870_ = stack[0].m_obj;
uint8_t v_report_1871_ = stack[1].m_num;
uint8_t v_a_1872_ = stack[2].m_num;
lean_object* v_a_1873_ = stack[3].m_obj;
lean_object* v_a_1874_ = stack[4].m_obj;
lean_object* v_a_1875_ = stack[5].m_obj;
lean_object* v_a_1876_ = stack[6].m_obj;
lean_object* v_a_1877_ = stack[7].m_obj;
lean_object* v_a_1878_ = stack[8].m_obj;
lean_object* v_res_1986_;
v_res_1986_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_1870_, v_report_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
stack->m_obj
 = v_res_1986_;
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_2003_ = l_Lean_mkConst(v___x_2002_, v___x_2001_);
return v___x_2003_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_2004_, lean_object* v_prop_2005_, lean_object* v_inst_2006_, lean_object* v_e_2007_, uint8_t v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; 
lean_inc_ref(v_prop_2005_);
v___x_2016_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2005_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2059_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2059_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2059_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___y_2022_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_2017_);
v___x_2028_ = l_Lean_Expr_app___override(v___x_2027_, v_a_2017_);
if (v_a_2008_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2028_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___y_2032_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
if (lean_obj_tag(v_a_2030_) == 0)
{
lean_inc_ref(v_inst_2006_);
v___y_2032_ = v_inst_2006_;
goto v___jp_2031_;
}
else
{
lean_object* v_val_2048_; 
v_val_2048_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v_a_2030_, 1);
v___y_2032_ = v_val_2048_;
goto v___jp_2031_;
}
v___jp_2031_:
{
lean_object* v___x_2033_; 
lean_inc_ref(v_inst_2006_);
v___x_2033_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_2006_, v___y_2032_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2047_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2047_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2047_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
size_t v___x_2038_; size_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_ptr_addr(v_prop_2005_);
lean_dec_ref(v_prop_2005_);
v___x_2039_ = lean_ptr_addr(v_a_2017_);
v___x_2040_ = lean_usize_dec_eq(v___x_2038_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_del_object(v___x_2036_);
lean_dec_ref(v_e_2007_);
lean_dec_ref(v_inst_2006_);
v___y_2022_ = v_a_2034_;
goto v___jp_2021_;
}
else
{
size_t v___x_2041_; size_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = lean_ptr_addr(v_inst_2006_);
lean_dec_ref(v_inst_2006_);
v___x_2042_ = lean_ptr_addr(v_a_2034_);
v___x_2043_ = lean_usize_dec_eq(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_del_object(v___x_2036_);
lean_dec_ref(v_e_2007_);
v___y_2022_ = v_a_2034_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2045_; 
lean_dec(v_a_2034_);
lean_del_object(v___x_2019_);
lean_dec(v_a_2017_);
lean_dec_ref(v_g_2004_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v_e_2007_);
v___x_2045_ = v___x_2036_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_e_2007_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
else
{
lean_del_object(v___x_2019_);
lean_dec(v_a_2017_);
lean_dec_ref(v_e_2007_);
lean_dec_ref(v_inst_2006_);
lean_dec_ref(v_prop_2005_);
lean_dec_ref(v_g_2004_);
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_2019_);
lean_dec(v_a_2017_);
lean_dec_ref(v_e_2007_);
lean_dec_ref(v_inst_2006_);
lean_dec_ref(v_prop_2005_);
lean_dec_ref(v_g_2004_);
v_a_2049_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2029_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2029_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
uint8_t v___x_2057_; lean_object* v___x_2058_; 
lean_del_object(v___x_2019_);
lean_dec(v_a_2017_);
lean_dec_ref(v_e_2007_);
lean_dec_ref(v_prop_2005_);
lean_dec_ref(v_g_2004_);
v___x_2057_ = 0;
v___x_2058_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_2006_, v___x_2028_, v___x_2057_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2058_;
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = l_Lean_mkAppB(v_g_2004_, v_a_2017_, v___y_2022_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
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
lean_dec_ref(v_e_2007_);
lean_dec_ref(v_inst_2006_);
lean_dec_ref(v_prop_2005_);
lean_dec_ref(v_g_2004_);
return v___x_2016_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_2004_ = stack[0].m_obj;
lean_object* v_prop_2005_ = stack[1].m_obj;
lean_object* v_inst_2006_ = stack[2].m_obj;
lean_object* v_e_2007_ = stack[3].m_obj;
uint8_t v_a_2008_ = stack[4].m_num;
lean_object* v_a_2009_ = stack[5].m_obj;
lean_object* v_a_2010_ = stack[6].m_obj;
lean_object* v_a_2011_ = stack[7].m_obj;
lean_object* v_a_2012_ = stack[8].m_obj;
lean_object* v_a_2013_ = stack[9].m_obj;
lean_object* v_a_2014_ = stack[10].m_obj;
lean_object* v_res_2060_;
v_res_2060_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2004_, v_prop_2005_, v_inst_2006_, v_e_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
stack->m_obj
 = v_res_2060_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2061_, lean_object* v_prop_2062_, lean_object* v_h_2063_, lean_object* v_e_2064_, uint8_t v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
if (v_a_2065_ == 0)
{
lean_object* v___x_2073_; lean_object* v_canon_2074_; lean_object* v_cache_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_st_ref_get(v_a_2067_);
v_canon_2074_ = lean_ctor_get(v___x_2073_, 10);
lean_inc_ref(v_canon_2074_);
lean_dec(v___x_2073_);
v_cache_2075_ = lean_ctor_get(v_canon_2074_, 0);
lean_inc_ref(v_cache_2075_);
lean_dec_ref(v_canon_2074_);
v___x_2076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2075_, v_e_2064_);
lean_dec_ref(v_cache_2075_);
if (lean_obj_tag(v___x_2076_) == 1)
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_e_2064_);
lean_dec_ref(v_h_2063_);
lean_dec_ref(v_prop_2062_);
lean_dec_ref(v_g_2061_);
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 0);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_val_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v___x_2085_; 
lean_dec(v___x_2076_);
lean_inc_ref(v_e_2064_);
v___x_2085_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2061_, v_prop_2062_, v_h_2063_, v_e_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2125_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2125_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2125_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v_canon_2091_; lean_object* v_share_2092_; lean_object* v_maxFVar_2093_; lean_object* v_proofInstInfo_2094_; lean_object* v_proofInstInfoFVar_2095_; lean_object* v_inferType_2096_; lean_object* v_getLevel_2097_; lean_object* v_congrInfo_2098_; lean_object* v_defEqI_2099_; lean_object* v_extensions_2100_; lean_object* v_issues_2101_; lean_object* v_instanceOverrides_2102_; uint8_t v_debug_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2124_; 
v___x_2090_ = lean_st_ref_take(v_a_2067_);
v_canon_2091_ = lean_ctor_get(v___x_2090_, 10);
v_share_2092_ = lean_ctor_get(v___x_2090_, 0);
v_maxFVar_2093_ = lean_ctor_get(v___x_2090_, 1);
v_proofInstInfo_2094_ = lean_ctor_get(v___x_2090_, 2);
v_proofInstInfoFVar_2095_ = lean_ctor_get(v___x_2090_, 3);
v_inferType_2096_ = lean_ctor_get(v___x_2090_, 4);
v_getLevel_2097_ = lean_ctor_get(v___x_2090_, 5);
v_congrInfo_2098_ = lean_ctor_get(v___x_2090_, 6);
v_defEqI_2099_ = lean_ctor_get(v___x_2090_, 7);
v_extensions_2100_ = lean_ctor_get(v___x_2090_, 8);
v_issues_2101_ = lean_ctor_get(v___x_2090_, 9);
v_instanceOverrides_2102_ = lean_ctor_get(v___x_2090_, 11);
v_debug_2103_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*12);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2105_ = v___x_2090_;
v_isShared_2106_ = v_isSharedCheck_2124_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_instanceOverrides_2102_);
lean_inc(v_canon_2091_);
lean_inc(v_issues_2101_);
lean_inc(v_extensions_2100_);
lean_inc(v_defEqI_2099_);
lean_inc(v_congrInfo_2098_);
lean_inc(v_getLevel_2097_);
lean_inc(v_inferType_2096_);
lean_inc(v_proofInstInfoFVar_2095_);
lean_inc(v_proofInstInfo_2094_);
lean_inc(v_maxFVar_2093_);
lean_inc(v_share_2092_);
lean_dec(v___x_2090_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2124_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_cache_2107_; lean_object* v_cacheInType_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2123_; 
v_cache_2107_ = lean_ctor_get(v_canon_2091_, 0);
v_cacheInType_2108_ = lean_ctor_get(v_canon_2091_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_canon_2091_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2110_ = v_canon_2091_;
v_isShared_2111_ = v_isSharedCheck_2123_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_cacheInType_2108_);
lean_inc(v_cache_2107_);
lean_dec(v_canon_2091_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2123_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_inc(v_a_2086_);
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2107_, v_e_2064_, v_a_2086_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2112_);
v___x_2114_ = v___x_2110_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_cacheInType_2108_);
v___x_2114_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 10, v___x_2114_);
v___x_2116_ = v___x_2105_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_share_2092_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_maxFVar_2093_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_proofInstInfo_2094_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_proofInstInfoFVar_2095_);
lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_inferType_2096_);
lean_ctor_set(v_reuseFailAlloc_2121_, 5, v_getLevel_2097_);
lean_ctor_set(v_reuseFailAlloc_2121_, 6, v_congrInfo_2098_);
lean_ctor_set(v_reuseFailAlloc_2121_, 7, v_defEqI_2099_);
lean_ctor_set(v_reuseFailAlloc_2121_, 8, v_extensions_2100_);
lean_ctor_set(v_reuseFailAlloc_2121_, 9, v_issues_2101_);
lean_ctor_set(v_reuseFailAlloc_2121_, 10, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2121_, 11, v_instanceOverrides_2102_);
lean_ctor_set_uint8(v_reuseFailAlloc_2121_, sizeof(void*)*12, v_debug_2103_);
v___x_2116_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_st_ref_put(v_a_2067_, v___x_2116_);
if (v_isShared_2089_ == 0)
{
v___x_2119_ = v___x_2088_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2086_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2064_);
return v___x_2085_;
}
}
}
else
{
lean_object* v___x_2126_; lean_object* v_canon_2127_; lean_object* v_cacheInType_2128_; lean_object* v___x_2129_; 
v___x_2126_ = lean_st_ref_get(v_a_2067_);
v_canon_2127_ = lean_ctor_get(v___x_2126_, 10);
lean_inc_ref(v_canon_2127_);
lean_dec(v___x_2126_);
v_cacheInType_2128_ = lean_ctor_get(v_canon_2127_, 1);
lean_inc_ref(v_cacheInType_2128_);
lean_dec_ref(v_canon_2127_);
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2128_, v_e_2064_);
lean_dec_ref(v_cacheInType_2128_);
if (lean_obj_tag(v___x_2129_) == 1)
{
lean_object* v_val_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_e_2064_);
lean_dec_ref(v_h_2063_);
lean_dec_ref(v_prop_2062_);
lean_dec_ref(v_g_2061_);
v_val_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_val_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 0);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_object* v___x_2138_; 
lean_dec(v___x_2129_);
lean_inc_ref(v_e_2064_);
v___x_2138_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2061_, v_prop_2062_, v_h_2063_, v_e_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2178_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v_canon_2144_; lean_object* v_share_2145_; lean_object* v_maxFVar_2146_; lean_object* v_proofInstInfo_2147_; lean_object* v_proofInstInfoFVar_2148_; lean_object* v_inferType_2149_; lean_object* v_getLevel_2150_; lean_object* v_congrInfo_2151_; lean_object* v_defEqI_2152_; lean_object* v_extensions_2153_; lean_object* v_issues_2154_; lean_object* v_instanceOverrides_2155_; uint8_t v_debug_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2177_; 
v___x_2143_ = lean_st_ref_take(v_a_2067_);
v_canon_2144_ = lean_ctor_get(v___x_2143_, 10);
v_share_2145_ = lean_ctor_get(v___x_2143_, 0);
v_maxFVar_2146_ = lean_ctor_get(v___x_2143_, 1);
v_proofInstInfo_2147_ = lean_ctor_get(v___x_2143_, 2);
v_proofInstInfoFVar_2148_ = lean_ctor_get(v___x_2143_, 3);
v_inferType_2149_ = lean_ctor_get(v___x_2143_, 4);
v_getLevel_2150_ = lean_ctor_get(v___x_2143_, 5);
v_congrInfo_2151_ = lean_ctor_get(v___x_2143_, 6);
v_defEqI_2152_ = lean_ctor_get(v___x_2143_, 7);
v_extensions_2153_ = lean_ctor_get(v___x_2143_, 8);
v_issues_2154_ = lean_ctor_get(v___x_2143_, 9);
v_instanceOverrides_2155_ = lean_ctor_get(v___x_2143_, 11);
v_debug_2156_ = lean_ctor_get_uint8(v___x_2143_, sizeof(void*)*12);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2158_ = v___x_2143_;
v_isShared_2159_ = v_isSharedCheck_2177_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_instanceOverrides_2155_);
lean_inc(v_canon_2144_);
lean_inc(v_issues_2154_);
lean_inc(v_extensions_2153_);
lean_inc(v_defEqI_2152_);
lean_inc(v_congrInfo_2151_);
lean_inc(v_getLevel_2150_);
lean_inc(v_inferType_2149_);
lean_inc(v_proofInstInfoFVar_2148_);
lean_inc(v_proofInstInfo_2147_);
lean_inc(v_maxFVar_2146_);
lean_inc(v_share_2145_);
lean_dec(v___x_2143_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2177_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_cache_2160_; lean_object* v_cacheInType_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2176_; 
v_cache_2160_ = lean_ctor_get(v_canon_2144_, 0);
v_cacheInType_2161_ = lean_ctor_get(v_canon_2144_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_canon_2144_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2163_ = v_canon_2144_;
v_isShared_2164_ = v_isSharedCheck_2176_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_cacheInType_2161_);
lean_inc(v_cache_2160_);
lean_dec(v_canon_2144_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2176_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_inc(v_a_2139_);
v___x_2165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2161_, v_e_2064_, v_a_2139_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_cache_2160_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 10, v___x_2167_);
v___x_2169_ = v___x_2158_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_share_2145_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_maxFVar_2146_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_proofInstInfo_2147_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_proofInstInfoFVar_2148_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_inferType_2149_);
lean_ctor_set(v_reuseFailAlloc_2174_, 5, v_getLevel_2150_);
lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_congrInfo_2151_);
lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_defEqI_2152_);
lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_extensions_2153_);
lean_ctor_set(v_reuseFailAlloc_2174_, 9, v_issues_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 10, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 11, v_instanceOverrides_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*12, v_debug_2156_);
v___x_2169_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_st_ref_put(v_a_2067_, v___x_2169_);
if (v_isShared_2142_ == 0)
{
v___x_2172_ = v___x_2141_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2139_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2064_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_2061_ = stack[0].m_obj;
lean_object* v_prop_2062_ = stack[1].m_obj;
lean_object* v_h_2063_ = stack[2].m_obj;
lean_object* v_e_2064_ = stack[3].m_obj;
uint8_t v_a_2065_ = stack[4].m_num;
lean_object* v_a_2066_ = stack[5].m_obj;
lean_object* v_a_2067_ = stack[6].m_obj;
lean_object* v_a_2068_ = stack[7].m_obj;
lean_object* v_a_2069_ = stack[8].m_obj;
lean_object* v_a_2070_ = stack[9].m_obj;
lean_object* v_a_2071_ = stack[10].m_obj;
lean_object* v_res_2179_;
v_res_2179_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_2061_, v_prop_2062_, v_h_2063_, v_e_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
stack->m_obj
 = v_res_2179_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2180_, lean_object* v_prop_2181_, lean_object* v_h_2182_, lean_object* v_e_2183_, uint8_t v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_a_2193_; lean_object* v___y_2228_; 
if (v_a_2184_ == 0)
{
lean_object* v___x_2269_; lean_object* v_canon_2270_; lean_object* v_cache_2271_; lean_object* v___x_2272_; 
v___x_2269_ = lean_st_ref_get(v_a_2186_);
v_canon_2270_ = lean_ctor_get(v___x_2269_, 10);
lean_inc_ref(v_canon_2270_);
lean_dec(v___x_2269_);
v_cache_2271_ = lean_ctor_get(v_canon_2270_, 0);
lean_inc_ref(v_cache_2271_);
lean_dec_ref(v_canon_2270_);
v___x_2272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2271_, v_e_2183_);
lean_dec_ref(v_cache_2271_);
if (lean_obj_tag(v___x_2272_) == 1)
{
lean_object* v_val_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_e_2183_);
lean_dec_ref(v_h_2182_);
lean_dec_ref(v_prop_2181_);
lean_dec_ref(v_g_2180_);
v_val_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_val_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 0);
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_val_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v___x_2281_; 
lean_dec(v___x_2272_);
lean_inc_ref(v_prop_2181_);
v___x_2281_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2181_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc_n(v_a_2282_, 2);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2282_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___y_2286_; lean_object* v___y_2289_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_inc_ref(v_h_2182_);
v___y_2289_ = v_h_2182_;
goto v___jp_2288_;
}
else
{
lean_object* v_val_2296_; 
v_val_2296_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v_a_2284_, 1);
v___y_2289_ = v_val_2296_;
goto v___jp_2288_;
}
v___jp_2285_:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_mkAppB(v_g_2180_, v_a_2282_, v___y_2286_);
v_a_2193_ = v___x_2287_;
goto v___jp_2192_;
}
v___jp_2288_:
{
size_t v___x_2290_; size_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = lean_ptr_addr(v_prop_2181_);
lean_dec_ref(v_prop_2181_);
v___x_2291_ = lean_ptr_addr(v_a_2282_);
v___x_2292_ = lean_usize_dec_eq(v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v_h_2182_);
v___y_2286_ = v___y_2289_;
goto v___jp_2285_;
}
else
{
size_t v___x_2293_; size_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_ptr_addr(v_h_2182_);
lean_dec_ref(v_h_2182_);
v___x_2294_ = lean_ptr_addr(v___y_2289_);
v___x_2295_ = lean_usize_dec_eq(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
v___y_2286_ = v___y_2289_;
goto v___jp_2285_;
}
else
{
lean_dec_ref(v___y_2289_);
lean_dec(v_a_2282_);
lean_dec_ref(v_g_2180_);
lean_inc_ref(v_e_2183_);
v_a_2193_ = v_e_2183_;
goto v___jp_2192_;
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_a_2282_);
lean_dec_ref(v_e_2183_);
lean_dec_ref(v_h_2182_);
lean_dec_ref(v_prop_2181_);
lean_dec_ref(v_g_2180_);
v_a_2297_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2283_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2283_);
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
else
{
lean_dec_ref(v_h_2182_);
lean_dec_ref(v_prop_2181_);
lean_dec_ref(v_g_2180_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2305_; 
v_a_2305_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2281_, 1);
v_a_2193_ = v_a_2305_;
goto v___jp_2192_;
}
else
{
lean_dec_ref(v_e_2183_);
return v___x_2281_;
}
}
}
}
else
{
lean_object* v___x_2306_; lean_object* v_canon_2307_; lean_object* v_cacheInType_2308_; lean_object* v___x_2309_; 
lean_dec_ref(v_g_2180_);
v___x_2306_ = lean_st_ref_get(v_a_2186_);
v_canon_2307_ = lean_ctor_get(v___x_2306_, 10);
lean_inc_ref(v_canon_2307_);
lean_dec(v___x_2306_);
v_cacheInType_2308_ = lean_ctor_get(v_canon_2307_, 1);
lean_inc_ref(v_cacheInType_2308_);
lean_dec_ref(v_canon_2307_);
v___x_2309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2308_, v_e_2183_);
lean_dec_ref(v_cacheInType_2308_);
if (lean_obj_tag(v___x_2309_) == 1)
{
lean_object* v_val_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_e_2183_);
lean_dec_ref(v_h_2182_);
lean_dec_ref(v_prop_2181_);
v_val_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_val_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 0);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_val_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v___x_2318_; 
lean_dec(v___x_2309_);
v___x_2318_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2181_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = 0;
v___x_2321_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2182_, v_a_2319_, v___x_2320_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
v___y_2228_ = v___x_2321_;
goto v___jp_2227_;
}
else
{
lean_dec_ref(v_h_2182_);
v___y_2228_ = v___x_2318_;
goto v___jp_2227_;
}
}
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v_canon_2195_; lean_object* v_share_2196_; lean_object* v_maxFVar_2197_; lean_object* v_proofInstInfo_2198_; lean_object* v_proofInstInfoFVar_2199_; lean_object* v_inferType_2200_; lean_object* v_getLevel_2201_; lean_object* v_congrInfo_2202_; lean_object* v_defEqI_2203_; lean_object* v_extensions_2204_; lean_object* v_issues_2205_; lean_object* v_instanceOverrides_2206_; uint8_t v_debug_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2226_; 
v___x_2194_ = lean_st_ref_take(v_a_2186_);
v_canon_2195_ = lean_ctor_get(v___x_2194_, 10);
v_share_2196_ = lean_ctor_get(v___x_2194_, 0);
v_maxFVar_2197_ = lean_ctor_get(v___x_2194_, 1);
v_proofInstInfo_2198_ = lean_ctor_get(v___x_2194_, 2);
v_proofInstInfoFVar_2199_ = lean_ctor_get(v___x_2194_, 3);
v_inferType_2200_ = lean_ctor_get(v___x_2194_, 4);
v_getLevel_2201_ = lean_ctor_get(v___x_2194_, 5);
v_congrInfo_2202_ = lean_ctor_get(v___x_2194_, 6);
v_defEqI_2203_ = lean_ctor_get(v___x_2194_, 7);
v_extensions_2204_ = lean_ctor_get(v___x_2194_, 8);
v_issues_2205_ = lean_ctor_get(v___x_2194_, 9);
v_instanceOverrides_2206_ = lean_ctor_get(v___x_2194_, 11);
v_debug_2207_ = lean_ctor_get_uint8(v___x_2194_, sizeof(void*)*12);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2209_ = v___x_2194_;
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_instanceOverrides_2206_);
lean_inc(v_canon_2195_);
lean_inc(v_issues_2205_);
lean_inc(v_extensions_2204_);
lean_inc(v_defEqI_2203_);
lean_inc(v_congrInfo_2202_);
lean_inc(v_getLevel_2201_);
lean_inc(v_inferType_2200_);
lean_inc(v_proofInstInfoFVar_2199_);
lean_inc(v_proofInstInfo_2198_);
lean_inc(v_maxFVar_2197_);
lean_inc(v_share_2196_);
lean_dec(v___x_2194_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_cache_2211_; lean_object* v_cacheInType_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2225_; 
v_cache_2211_ = lean_ctor_get(v_canon_2195_, 0);
v_cacheInType_2212_ = lean_ctor_get(v_canon_2195_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_canon_2195_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2214_ = v_canon_2195_;
v_isShared_2215_ = v_isSharedCheck_2225_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_cacheInType_2212_);
lean_inc(v_cache_2211_);
lean_dec(v_canon_2195_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2225_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_inc_ref(v_a_2193_);
v___x_2216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2211_, v_e_2183_, v_a_2193_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_cacheInType_2212_);
v___x_2218_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 10, v___x_2218_);
v___x_2220_ = v___x_2209_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_share_2196_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_maxFVar_2197_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_proofInstInfo_2198_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_proofInstInfoFVar_2199_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_inferType_2200_);
lean_ctor_set(v_reuseFailAlloc_2223_, 5, v_getLevel_2201_);
lean_ctor_set(v_reuseFailAlloc_2223_, 6, v_congrInfo_2202_);
lean_ctor_set(v_reuseFailAlloc_2223_, 7, v_defEqI_2203_);
lean_ctor_set(v_reuseFailAlloc_2223_, 8, v_extensions_2204_);
lean_ctor_set(v_reuseFailAlloc_2223_, 9, v_issues_2205_);
lean_ctor_set(v_reuseFailAlloc_2223_, 10, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2223_, 11, v_instanceOverrides_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*12, v_debug_2207_);
v___x_2220_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_st_ref_put(v_a_2186_, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2193_);
return v___x_2222_;
}
}
}
}
}
v___jp_2227_:
{
if (lean_obj_tag(v___y_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2268_; 
v_a_2229_ = lean_ctor_get(v___y_2228_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2228_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2231_ = v___y_2228_;
v_isShared_2232_ = v_isSharedCheck_2268_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___y_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2268_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v_canon_2234_; lean_object* v_share_2235_; lean_object* v_maxFVar_2236_; lean_object* v_proofInstInfo_2237_; lean_object* v_proofInstInfoFVar_2238_; lean_object* v_inferType_2239_; lean_object* v_getLevel_2240_; lean_object* v_congrInfo_2241_; lean_object* v_defEqI_2242_; lean_object* v_extensions_2243_; lean_object* v_issues_2244_; lean_object* v_instanceOverrides_2245_; uint8_t v_debug_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2267_; 
v___x_2233_ = lean_st_ref_take(v_a_2186_);
v_canon_2234_ = lean_ctor_get(v___x_2233_, 10);
v_share_2235_ = lean_ctor_get(v___x_2233_, 0);
v_maxFVar_2236_ = lean_ctor_get(v___x_2233_, 1);
v_proofInstInfo_2237_ = lean_ctor_get(v___x_2233_, 2);
v_proofInstInfoFVar_2238_ = lean_ctor_get(v___x_2233_, 3);
v_inferType_2239_ = lean_ctor_get(v___x_2233_, 4);
v_getLevel_2240_ = lean_ctor_get(v___x_2233_, 5);
v_congrInfo_2241_ = lean_ctor_get(v___x_2233_, 6);
v_defEqI_2242_ = lean_ctor_get(v___x_2233_, 7);
v_extensions_2243_ = lean_ctor_get(v___x_2233_, 8);
v_issues_2244_ = lean_ctor_get(v___x_2233_, 9);
v_instanceOverrides_2245_ = lean_ctor_get(v___x_2233_, 11);
v_debug_2246_ = lean_ctor_get_uint8(v___x_2233_, sizeof(void*)*12);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2248_ = v___x_2233_;
v_isShared_2249_ = v_isSharedCheck_2267_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_instanceOverrides_2245_);
lean_inc(v_canon_2234_);
lean_inc(v_issues_2244_);
lean_inc(v_extensions_2243_);
lean_inc(v_defEqI_2242_);
lean_inc(v_congrInfo_2241_);
lean_inc(v_getLevel_2240_);
lean_inc(v_inferType_2239_);
lean_inc(v_proofInstInfoFVar_2238_);
lean_inc(v_proofInstInfo_2237_);
lean_inc(v_maxFVar_2236_);
lean_inc(v_share_2235_);
lean_dec(v___x_2233_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2267_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_cache_2250_; lean_object* v_cacheInType_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2266_; 
v_cache_2250_ = lean_ctor_get(v_canon_2234_, 0);
v_cacheInType_2251_ = lean_ctor_get(v_canon_2234_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_canon_2234_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2253_ = v_canon_2234_;
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_cacheInType_2251_);
lean_inc(v_cache_2250_);
lean_dec(v_canon_2234_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_inc(v_a_2229_);
v___x_2255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2251_, v_e_2183_, v_a_2229_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_cache_2250_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2259_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 10, v___x_2257_);
v___x_2259_ = v___x_2248_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_share_2235_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_maxFVar_2236_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_proofInstInfo_2237_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_proofInstInfoFVar_2238_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_inferType_2239_);
lean_ctor_set(v_reuseFailAlloc_2264_, 5, v_getLevel_2240_);
lean_ctor_set(v_reuseFailAlloc_2264_, 6, v_congrInfo_2241_);
lean_ctor_set(v_reuseFailAlloc_2264_, 7, v_defEqI_2242_);
lean_ctor_set(v_reuseFailAlloc_2264_, 8, v_extensions_2243_);
lean_ctor_set(v_reuseFailAlloc_2264_, 9, v_issues_2244_);
lean_ctor_set(v_reuseFailAlloc_2264_, 10, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 11, v_instanceOverrides_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2264_, sizeof(void*)*12, v_debug_2246_);
v___x_2259_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_st_ref_put(v_a_2186_, v___x_2259_);
if (v_isShared_2232_ == 0)
{
v___x_2262_ = v___x_2231_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2229_);
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
}
}
}
else
{
lean_dec_ref(v_e_2183_);
return v___y_2228_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_2180_ = stack[0].m_obj;
lean_object* v_prop_2181_ = stack[1].m_obj;
lean_object* v_h_2182_ = stack[2].m_obj;
lean_object* v_e_2183_ = stack[3].m_obj;
uint8_t v_a_2184_ = stack[4].m_num;
lean_object* v_a_2185_ = stack[5].m_obj;
lean_object* v_a_2186_ = stack[6].m_obj;
lean_object* v_a_2187_ = stack[7].m_obj;
lean_object* v_a_2188_ = stack[8].m_obj;
lean_object* v_a_2189_ = stack[9].m_obj;
lean_object* v_a_2190_ = stack[10].m_obj;
lean_object* v_res_2322_;
v_res_2322_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_2180_, v_prop_2181_, v_h_2182_, v_e_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
stack->m_obj
 = v_res_2322_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2323_, lean_object* v_snd_2324_, lean_object* v_a_2325_, uint8_t v___x_2326_, lean_object* v_fst_2327_, lean_object* v___x_2328_, lean_object* v_____r_2329_, uint8_t v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_arg_x27_2339_; lean_object* v___x_2373_; 
lean_inc_ref(v___x_2323_);
v___x_2373_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2328_, v_a_2325_, v___x_2323_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; uint8_t v___x_2375_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = lean_unbox(v_a_2374_);
lean_dec(v_a_2374_);
switch(v___x_2375_)
{
case 0:
{
lean_object* v___x_2376_; 
lean_inc_ref(v___x_2323_);
v___x_2376_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2323_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v_arg_x27_2339_ = v_a_2377_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2378_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
case 1:
{
lean_object* v___x_2386_; 
lean_inc_ref(v___x_2323_);
v___x_2386_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2323_, v___y_2334_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = l_Lean_Expr_cleanupAnnotations(v_a_2387_);
v___x_2389_ = l_Lean_Expr_isApp(v___x_2388_);
if (v___x_2389_ == 0)
{
lean_dec_ref(v___x_2388_);
goto v___jp_2362_;
}
else
{
lean_object* v_arg_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_arg_2390_ = lean_ctor_get(v___x_2388_, 1);
lean_inc_ref(v_arg_2390_);
v___x_2391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2388_);
v___x_2392_ = l_Lean_Expr_isApp(v___x_2391_);
if (v___x_2392_ == 0)
{
lean_dec_ref(v___x_2391_);
lean_dec_ref(v_arg_2390_);
goto v___jp_2362_;
}
else
{
lean_object* v_arg_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_arg_2393_ = lean_ctor_get(v___x_2391_, 1);
lean_inc_ref(v_arg_2393_);
v___x_2394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2391_);
v___x_2395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2396_ = l_Lean_Expr_isConstOf(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2398_ = l_Lean_Expr_isConstOf(v___x_2394_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_dec_ref(v___x_2394_);
lean_dec_ref(v_arg_2393_);
lean_dec_ref(v_arg_2390_);
goto v___jp_2362_;
}
else
{
lean_object* v___x_2399_; 
lean_inc_ref(v___x_2323_);
v___x_2399_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2394_, v_arg_2393_, v_arg_2390_, v___x_2323_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v_arg_x27_2339_ = v_a_2400_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2401_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2399_);
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
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_2409_; 
lean_inc_ref(v___x_2323_);
v___x_2409_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2394_, v_arg_2393_, v_arg_2390_, v___x_2323_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v_arg_x27_2339_ = v_a_2410_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2411_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2409_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2419_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2386_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2386_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
default: 
{
goto v___jp_2351_;
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2427_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2373_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2373_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
v___jp_2338_:
{
size_t v___x_2340_; size_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2340_ = lean_ptr_addr(v___x_2323_);
lean_dec_ref(v___x_2323_);
v___x_2341_ = lean_ptr_addr(v_arg_x27_2339_);
v___x_2342_ = lean_usize_dec_eq(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec(v_fst_2327_);
v___x_2343_ = lean_array_fset(v_snd_2324_, v_a_2325_, v_arg_x27_2339_);
v___x_2344_ = lean_box(v___x_2326_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2343_);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec_ref(v_arg_x27_2339_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_fst_2327_);
lean_ctor_set(v___x_2348_, 1, v_snd_2324_);
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
v___jp_2351_:
{
lean_object* v___x_2352_; 
lean_inc_ref(v___x_2323_);
v___x_2352_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2323_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v_arg_x27_2339_ = v_a_2353_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2354_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2352_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
v___jp_2362_:
{
lean_object* v___x_2363_; 
lean_inc_ref(v___x_2323_);
v___x_2363_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2323_, v___x_2326_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_arg_x27_2339_ = v_a_2364_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_fst_2327_);
lean_dec(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v_a_2365_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2323_ = stack[0].m_obj;
lean_object* v_snd_2324_ = stack[1].m_obj;
lean_object* v_a_2325_ = stack[2].m_obj;
uint8_t v___x_2326_ = stack[3].m_num;
lean_object* v_fst_2327_ = stack[4].m_obj;
lean_object* v___x_2328_ = stack[5].m_obj;
lean_object* v_____r_2329_ = stack[6].m_obj;
uint8_t v___y_2330_ = stack[7].m_num;
lean_object* v___y_2331_ = stack[8].m_obj;
lean_object* v___y_2332_ = stack[9].m_obj;
lean_object* v___y_2333_ = stack[10].m_obj;
lean_object* v___y_2334_ = stack[11].m_obj;
lean_object* v___y_2335_ = stack[12].m_obj;
lean_object* v___y_2336_ = stack[13].m_obj;
lean_object* v_res_2435_;
v_res_2435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2323_, v_snd_2324_, v_a_2325_, v___x_2326_, v_fst_2327_, v___x_2328_, v_____r_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
stack->m_obj
 = v_res_2435_;
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2440_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2441_ = l_Lean_Name_append(v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2444_ = l_Lean_stringToMessageData(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2447_ = l_Lean_stringToMessageData(v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2450_ = l_Lean_stringToMessageData(v___x_2449_);
return v___x_2450_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2451_, lean_object* v___x_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_, uint8_t v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___y_2464_; uint8_t v___x_2486_; 
v___x_2486_ = lean_nat_dec_lt(v_a_2453_, v_upperBound_2451_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v_a_2453_);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_b_2454_);
return v___x_2487_;
}
else
{
lean_object* v_toCold_2488_; lean_object* v_options_2489_; lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2555_; 
v_toCold_2488_ = lean_ctor_get(v___y_2460_, 0);
v_options_2489_ = lean_ctor_get(v_toCold_2488_, 2);
v_fst_2490_ = lean_ctor_get(v_b_2454_, 0);
v_snd_2491_ = lean_ctor_get(v_b_2454_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_b_2454_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2493_ = v_b_2454_;
v_isShared_2494_ = v_isSharedCheck_2555_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
lean_dec(v_b_2454_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2555_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_inheritedTraceOptions_2495_; uint8_t v_hasTrace_2496_; lean_object* v___x_2497_; 
v_inheritedTraceOptions_2495_ = lean_ctor_get(v_toCold_2488_, 11);
v_hasTrace_2496_ = lean_ctor_get_uint8(v_options_2489_, sizeof(void*)*1);
v___x_2497_ = lean_array_fget(v_snd_2491_, v_a_2453_);
if (v_hasTrace_2496_ == 0)
{
lean_del_object(v___x_2493_);
goto v___jp_2498_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2502_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2495_, v_options_2489_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_del_object(v___x_2493_);
goto v___jp_2498_;
}
else
{
lean_object* v___x_2504_; 
lean_inc(v___x_2497_);
v___x_2504_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2452_, v_a_2453_, v___x_2497_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___x_2497_);
v___x_2506_ = lean_infer_type(v___x_2497_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; lean_object* v___y_2510_; uint8_t v___x_2534_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2534_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
switch(v___x_2534_)
{
case 0:
{
lean_object* v___x_2535_; 
v___x_2535_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2510_ = v___x_2535_;
goto v___jp_2509_;
}
case 1:
{
lean_object* v___x_2536_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2510_ = v___x_2536_;
goto v___jp_2509_;
}
case 2:
{
lean_object* v___x_2537_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2510_ = v___x_2537_;
goto v___jp_2509_;
}
default: 
{
lean_object* v___x_2538_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2510_ = v___x_2538_;
goto v___jp_2509_;
}
}
v___jp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2513_; 
lean_inc(v___y_2510_);
v___x_2511_ = l_Lean_MessageData_ofFormat(v___y_2510_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 7);
lean_ctor_set(v___x_2493_, 1, v___x_2511_);
lean_ctor_set(v___x_2493_, 0, v___x_2508_);
v___x_2513_ = v___x_2493_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2514_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_inc(v___x_2497_);
v___x_2516_ = l_Lean_MessageData_ofExpr(v___x_2497_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = l_Lean_MessageData_ofExpr(v_a_2507_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2501_, v___x_2521_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2524_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2497_, v_snd_2491_, v_a_2453_, v___x_2486_, v_fst_2490_, v___x_2452_, v_a_2523_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
v___y_2464_ = v___x_2524_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v___x_2497_);
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_dec(v_a_2453_);
v_a_2525_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2522_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2522_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2505_);
lean_dec(v___x_2497_);
lean_del_object(v___x_2493_);
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_dec(v_a_2453_);
v_a_2539_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2506_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2506_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v___x_2497_);
lean_del_object(v___x_2493_);
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_dec(v_a_2453_);
v_a_2547_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2504_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2504_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
v___jp_2498_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_box(0);
v___x_2500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2497_, v_snd_2491_, v_a_2453_, v___x_2486_, v_fst_2490_, v___x_2452_, v___x_2499_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
v___y_2464_ = v___x_2500_;
goto v___jp_2463_;
}
}
}
v___jp_2463_:
{
if (lean_obj_tag(v___y_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2477_; 
v_a_2465_ = lean_ctor_get(v___y_2464_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___y_2464_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2467_ = v___y_2464_;
v_isShared_2468_ = v_isSharedCheck_2477_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___y_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2477_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
if (lean_obj_tag(v_a_2465_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; 
lean_dec(v_a_2453_);
v_a_2469_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v_a_2465_, 1);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_a_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_del_object(v___x_2467_);
v_a_2473_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v_a_2465_, 1);
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v_a_2453_, v___x_2474_);
lean_dec(v_a_2453_);
v_a_2453_ = v___x_2475_;
v_b_2454_ = v_a_2473_;
goto _start;
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2453_);
v_a_2478_ = lean_ctor_get(v___y_2464_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___y_2464_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___y_2464_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___y_2464_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2451_ = stack[0].m_obj;
lean_object* v___x_2452_ = stack[1].m_obj;
lean_object* v_a_2453_ = stack[2].m_obj;
lean_object* v_b_2454_ = stack[3].m_obj;
uint8_t v___y_2455_ = stack[4].m_num;
lean_object* v___y_2456_ = stack[5].m_obj;
lean_object* v___y_2457_ = stack[6].m_obj;
lean_object* v___y_2458_ = stack[7].m_obj;
lean_object* v___y_2459_ = stack[8].m_obj;
lean_object* v___y_2460_ = stack[9].m_obj;
lean_object* v___y_2461_ = stack[10].m_obj;
lean_object* v_res_2556_;
v_res_2556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_2451_, v___x_2452_, v_a_2453_, v_b_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
stack->m_obj
 = v_res_2556_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, uint8_t v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___y_2570_; uint8_t v_modified_2571_; lean_object* v_f_2572_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v_args_2628_; uint8_t v_modified_2629_; uint8_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; 
if (lean_obj_tag(v_x_2558_) == 5)
{
lean_object* v_fn_2665_; lean_object* v_arg_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_fn_2665_ = lean_ctor_get(v_x_2558_, 0);
lean_inc_ref(v_fn_2665_);
v_arg_2666_ = lean_ctor_get(v_x_2558_, 1);
lean_inc_ref(v_arg_2666_);
lean_dec_ref_known(v_x_2558_, 2);
v___x_2667_ = lean_array_set(v_x_2559_, v_x_2560_, v_arg_2666_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_sub(v_x_2560_, v___x_2668_);
lean_dec(v_x_2560_);
v_x_2558_ = v_fn_2665_;
v_x_2559_ = v___x_2667_;
v_x_2560_ = v___x_2669_;
goto _start;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
lean_dec(v_x_2560_);
v___x_2671_ = lean_array_get_size(v_x_2559_);
v___x_2672_ = lean_unsigned_to_nat(2u);
v___x_2673_ = lean_nat_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
v___y_2644_ = v___y_2561_;
v___y_2645_ = v___y_2562_;
v___y_2646_ = v___y_2563_;
v___y_2647_ = v___y_2564_;
v___y_2648_ = v___y_2565_;
v___y_2649_ = v___y_2566_;
v___y_2650_ = v___y_2567_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = l_Lean_instInhabitedExpr;
v___x_2675_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2676_ = l_Lean_Expr_isConstOf(v_x_2558_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2678_ = l_Lean_Expr_isConstOf(v_x_2558_, v___x_2677_);
if (v___x_2678_ == 0)
{
v___y_2644_ = v___y_2561_;
v___y_2645_ = v___y_2562_;
v___y_2646_ = v___y_2563_;
v___y_2647_ = v___y_2564_;
v___y_2648_ = v___y_2565_;
v___y_2649_ = v___y_2566_;
v___y_2650_ = v___y_2567_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = lean_array_get(v___x_2674_, v_x_2559_, v___x_2679_);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = lean_array_get(v___x_2674_, v_x_2559_, v___x_2681_);
lean_dec_ref(v_x_2559_);
v___x_2683_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2558_, v___x_2680_, v___x_2682_, v_e_2557_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2683_;
}
}
else
{
lean_object* v___x_2684_; lean_object* v_prop_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_unsigned_to_nat(0u);
v_prop_2685_ = lean_array_get_borrowed(v___x_2674_, v_x_2559_, v___x_2684_);
lean_inc(v_prop_2685_);
v___x_2686_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2685_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2703_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2703_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2703_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
size_t v___x_2691_; size_t v___x_2692_; uint8_t v___x_2693_; 
v___x_2691_ = lean_ptr_addr(v_prop_2685_);
v___x_2692_ = lean_ptr_addr(v_a_2687_);
v___x_2693_ = lean_usize_dec_eq(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_dec_ref(v_e_2557_);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_array_get(v___x_2674_, v_x_2559_, v___x_2694_);
lean_dec_ref(v_x_2559_);
v___x_2696_ = l_Lean_mkAppB(v_x_2558_, v_a_2687_, v___x_2695_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2696_);
v___x_2698_ = v___x_2689_;
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
else
{
lean_object* v___x_2701_; 
lean_dec(v_a_2687_);
lean_dec_ref(v_x_2559_);
lean_dec_ref(v_x_2558_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_e_2557_);
v___x_2701_ = v___x_2689_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_e_2557_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_dec_ref(v_x_2559_);
lean_dec_ref(v_x_2558_);
lean_dec_ref(v_e_2557_);
return v___x_2686_;
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_box(0);
lean_inc_ref(v_f_2572_);
v___x_2581_ = l_Lean_Meta_getFunInfo(v_f_2572_, v___x_2580_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_paramInfo_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2617_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_paramInfo_2583_ = lean_ctor_get(v_a_2582_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2582_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v_a_2582_, 1);
lean_dec(v_unused_2618_);
v___x_2585_ = v_a_2582_;
v_isShared_2586_ = v_isSharedCheck_2617_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_paramInfo_2583_);
lean_dec(v_a_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2617_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2587_ = lean_array_get_size(v___y_2570_);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_box(v_modified_2571_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___y_2570_);
lean_ctor_set(v___x_2585_, 0, v___x_2589_);
v___x_2591_ = v___x_2585_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___y_2570_);
v___x_2591_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2587_, v_paramInfo_2583_, v___x_2588_, v___x_2591_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v_paramInfo_2583_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2607_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2597_; uint8_t v___x_2598_; 
v_fst_2597_ = lean_ctor_get(v_a_2593_, 0);
v___x_2598_ = lean_unbox(v_fst_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2600_; 
lean_dec(v_a_2593_);
lean_dec_ref(v_f_2572_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_e_2557_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_e_2557_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
else
{
lean_object* v_snd_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec_ref(v_e_2557_);
v_snd_2602_ = lean_ctor_get(v_a_2593_, 1);
lean_inc(v_snd_2602_);
lean_dec(v_a_2593_);
v___x_2603_ = l_Lean_mkAppN(v_f_2572_, v_snd_2602_);
lean_dec(v_snd_2602_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2603_);
v___x_2605_ = v___x_2595_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v_f_2572_);
lean_dec_ref(v_e_2557_);
v_a_2608_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2592_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2592_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_f_2572_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v_e_2557_);
v_a_2619_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2581_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2581_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
v___jp_2627_:
{
lean_object* v___x_2637_; 
lean_inc_ref(v_x_2558_);
v___x_2637_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2558_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; size_t v___x_2639_; size_t v___x_2640_; uint8_t v___x_2641_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = lean_ptr_addr(v_x_2558_);
v___x_2640_ = lean_ptr_addr(v_a_2638_);
v___x_2641_ = lean_usize_dec_eq(v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
uint8_t v___x_2642_; 
lean_dec_ref(v_x_2558_);
v___x_2642_ = 1;
v___y_2570_ = v_args_2628_;
v_modified_2571_ = v___x_2642_;
v_f_2572_ = v_a_2638_;
v___y_2573_ = v___y_2630_;
v___y_2574_ = v___y_2631_;
v___y_2575_ = v___y_2632_;
v___y_2576_ = v___y_2633_;
v___y_2577_ = v___y_2634_;
v___y_2578_ = v___y_2635_;
v___y_2579_ = v___y_2636_;
goto v___jp_2569_;
}
else
{
lean_dec(v_a_2638_);
v___y_2570_ = v_args_2628_;
v_modified_2571_ = v_modified_2629_;
v_f_2572_ = v_x_2558_;
v___y_2573_ = v___y_2630_;
v___y_2574_ = v___y_2631_;
v___y_2575_ = v___y_2632_;
v___y_2576_ = v___y_2633_;
v___y_2577_ = v___y_2634_;
v___y_2578_ = v___y_2635_;
v___y_2579_ = v___y_2636_;
goto v___jp_2569_;
}
}
else
{
lean_dec_ref(v_args_2628_);
lean_dec_ref(v_x_2558_);
lean_dec_ref(v_e_2557_);
return v___x_2637_;
}
}
v___jp_2643_:
{
uint8_t v_modified_2651_; lean_object* v___x_2652_; uint8_t v_modified_2653_; 
v_modified_2651_ = 0;
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2653_ = l_Lean_Expr_isConstOf(v_x_2558_, v___x_2652_);
if (v_modified_2653_ == 0)
{
v_args_2628_ = v_x_2559_;
v_modified_2629_ = v_modified_2651_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
v___y_2632_ = v___y_2646_;
v___y_2633_ = v___y_2647_;
v___y_2634_ = v___y_2648_;
v___y_2635_ = v___y_2649_;
v___y_2636_ = v___y_2650_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2654_; 
lean_inc_ref(v_x_2559_);
v___x_2654_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2559_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
if (lean_obj_tag(v_a_2655_) == 1)
{
lean_object* v_val_2656_; 
lean_dec_ref(v_x_2559_);
v_val_2656_ = lean_ctor_get(v_a_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_a_2655_, 1);
v_args_2628_ = v_val_2656_;
v_modified_2629_ = v_modified_2653_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
v___y_2632_ = v___y_2646_;
v___y_2633_ = v___y_2647_;
v___y_2634_ = v___y_2648_;
v___y_2635_ = v___y_2649_;
v___y_2636_ = v___y_2650_;
goto v___jp_2627_;
}
else
{
lean_dec(v_a_2655_);
v_args_2628_ = v_x_2559_;
v_modified_2629_ = v_modified_2651_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
v___y_2632_ = v___y_2646_;
v___y_2633_ = v___y_2647_;
v___y_2634_ = v___y_2648_;
v___y_2635_ = v___y_2649_;
v___y_2636_ = v___y_2650_;
goto v___jp_2627_;
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_x_2559_);
lean_dec_ref(v_x_2558_);
lean_dec_ref(v_e_2557_);
v_a_2657_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2654_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2654_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2557_ = stack[0].m_obj;
lean_object* v_x_2558_ = stack[1].m_obj;
lean_object* v_x_2559_ = stack[2].m_obj;
lean_object* v_x_2560_ = stack[3].m_obj;
uint8_t v___y_2561_ = stack[4].m_num;
lean_object* v___y_2562_ = stack[5].m_obj;
lean_object* v___y_2563_ = stack[6].m_obj;
lean_object* v___y_2564_ = stack[7].m_obj;
lean_object* v___y_2565_ = stack[8].m_obj;
lean_object* v___y_2566_ = stack[9].m_obj;
lean_object* v___y_2567_ = stack[10].m_obj;
lean_object* v_res_2704_;
v_res_2704_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2557_, v_x_2558_, v_x_2559_, v_x_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
stack->m_obj
 = v_res_2704_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2705_, uint8_t v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_dummy_2714_; lean_object* v_nargs_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_dummy_2714_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2715_ = l_Lean_Expr_getAppNumArgs(v_e_2705_);
lean_inc(v_nargs_2715_);
v___x_2716_ = lean_mk_array(v_nargs_2715_, v_dummy_2714_);
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_sub(v_nargs_2715_, v___x_2717_);
lean_dec(v_nargs_2715_);
lean_inc_ref(v_e_2705_);
v___x_2719_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2705_, v_e_2705_, v___x_2716_, v___x_2718_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
return v___x_2719_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2705_ = stack[0].m_obj;
uint8_t v_a_2706_ = stack[1].m_num;
lean_object* v_a_2707_ = stack[2].m_obj;
lean_object* v_a_2708_ = stack[3].m_obj;
lean_object* v_a_2709_ = stack[4].m_obj;
lean_object* v_a_2710_ = stack[5].m_obj;
lean_object* v_a_2711_ = stack[6].m_obj;
lean_object* v_a_2712_ = stack[7].m_obj;
lean_object* v_res_2720_;
v_res_2720_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
stack->m_obj
 = v_res_2720_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2721_, uint8_t v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
uint8_t v___x_2750_; 
lean_inc_ref(v_e_2721_);
v___x_2750_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2721_);
if (v___x_2750_ == 0)
{
lean_object* v_f_2751_; 
v_f_2751_ = l_Lean_Expr_getAppFn(v_e_2721_);
if (lean_obj_tag(v_f_2751_) == 4)
{
lean_object* v_declName_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_declName_2752_ = lean_ctor_get(v_f_2751_, 0);
lean_inc(v_declName_2752_);
lean_dec_ref_known(v_f_2751_, 2);
v___x_2753_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2754_ = lean_name_eq(v_declName_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_2756_ = lean_name_eq(v_declName_2752_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2758_ = lean_name_eq(v_declName_2752_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2760_ = lean_name_eq(v_declName_2752_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_2762_ = lean_name_eq(v_declName_2752_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2752_, v_a_2728_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2793_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2793_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2793_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
if (lean_obj_tag(v_a_2764_) == 1)
{
lean_object* v_val_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2766_);
v_val_2768_ = lean_ctor_get(v_a_2764_, 0);
lean_inc(v_val_2768_);
lean_dec_ref_known(v_a_2764_, 1);
lean_inc_ref(v_e_2721_);
v___x_2769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2768_, v_e_2721_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_val_2768_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2781_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
if (lean_obj_tag(v_a_2770_) == 0)
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_e_2721_);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_e_2721_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
lean_object* v_val_2777_; lean_object* v___x_2779_; 
lean_dec_ref(v_e_2721_);
v_val_2777_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_val_2777_);
lean_dec_ref_known(v_a_2770_, 1);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_val_2777_);
v___x_2779_ = v___x_2772_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_val_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v_e_2721_);
v_a_2782_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2769_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2769_);
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
else
{
lean_object* v___x_2791_; 
lean_dec(v_a_2764_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_e_2721_);
v___x_2791_ = v___x_2766_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_e_2721_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v_e_2721_);
v_a_2794_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2763_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2763_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_dec(v_declName_2752_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v_declName_2752_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v_declName_2752_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v_declName_2752_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v_declName_2752_);
goto v___jp_2730_;
}
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v_f_2751_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_e_2721_);
return v___x_2802_;
}
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_inc_ref(v_e_2721_);
v___x_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2803_, 0, v_e_2721_);
v___x_2804_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2803_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2838_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2838_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2838_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
if (lean_obj_tag(v_a_2805_) == 1)
{
lean_object* v_val_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
lean_dec_ref(v_e_2721_);
v_val_2809_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_val_2809_);
lean_dec_ref_known(v_a_2805_, 1);
v___x_2810_ = l_Lean_mkNatLit(v_val_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
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
lean_object* v___x_2814_; 
lean_del_object(v___x_2807_);
lean_dec(v_a_2805_);
lean_inc_ref(v_e_2721_);
v___x_2814_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2721_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2829_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2829_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2829_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
if (lean_obj_tag(v_a_2815_) == 1)
{
lean_object* v_val_2819_; lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_dec_ref(v_e_2721_);
v_val_2819_ = lean_ctor_get(v_a_2815_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v_a_2815_, 1);
v_fst_2820_ = lean_ctor_get(v_val_2819_, 0);
lean_inc(v_fst_2820_);
v_snd_2821_ = lean_ctor_get(v_val_2819_, 1);
lean_inc(v_snd_2821_);
lean_dec(v_val_2819_);
v___x_2822_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2820_, v_snd_2821_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2822_);
v___x_2824_ = v___x_2817_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
else
{
lean_object* v___x_2827_; 
lean_dec(v_a_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_e_2721_);
v___x_2827_ = v___x_2817_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_e_2721_);
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
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref(v_e_2721_);
v_a_2830_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2814_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2814_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_e_2721_);
v_a_2839_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2804_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2804_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
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
v___jp_2730_:
{
lean_object* v___x_2731_; 
lean_inc_ref(v_e_2721_);
v___x_2731_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2721_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2741_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
if (lean_obj_tag(v_a_2732_) == 1)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; 
lean_del_object(v___x_2734_);
lean_dec_ref(v_e_2721_);
v_val_2736_ = lean_ctor_get(v_a_2732_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v_a_2732_, 1);
v___x_2737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2736_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
return v___x_2737_;
}
else
{
lean_object* v___x_2739_; 
lean_dec(v_a_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v_e_2721_);
v___x_2739_ = v___x_2734_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_e_2721_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v_e_2721_);
v_a_2742_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2731_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2731_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2721_ = stack[0].m_obj;
uint8_t v_a_2722_ = stack[1].m_num;
lean_object* v_a_2723_ = stack[2].m_obj;
lean_object* v_a_2724_ = stack[3].m_obj;
lean_object* v_a_2725_ = stack[4].m_obj;
lean_object* v_a_2726_ = stack[5].m_obj;
lean_object* v_a_2727_ = stack[6].m_obj;
lean_object* v_a_2728_ = stack[7].m_obj;
lean_object* v_res_2847_;
v_res_2847_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
stack->m_obj
 = v_res_2847_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2848_, uint8_t v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2858_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
return v___x_2859_;
}
else
{
return v___x_2857_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2848_ = stack[0].m_obj;
uint8_t v_a_2849_ = stack[1].m_num;
lean_object* v_a_2850_ = stack[2].m_obj;
lean_object* v_a_2851_ = stack[3].m_obj;
lean_object* v_a_2852_ = stack[4].m_obj;
lean_object* v_a_2853_ = stack[5].m_obj;
lean_object* v_a_2854_ = stack[6].m_obj;
lean_object* v_a_2855_ = stack[7].m_obj;
lean_object* v_res_2860_;
v_res_2860_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
stack->m_obj
 = v_res_2860_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2861_, uint8_t v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2861_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
if (lean_obj_tag(v_a_2871_) == 0)
{
lean_object* v_val_2872_; lean_object* v___x_2873_; 
lean_dec_ref(v_e_2861_);
v_val_2872_ = lean_ctor_get(v_a_2871_, 0);
lean_inc_ref(v_val_2872_);
lean_dec_ref_known(v_a_2871_, 1);
v___x_2873_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2872_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_a_2871_);
v___x_2874_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2875_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2886_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2886_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2886_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
if (lean_obj_tag(v_a_2877_) == 0)
{
lean_object* v_val_2881_; lean_object* v___x_2882_; 
lean_del_object(v___x_2879_);
lean_dec(v_a_2875_);
v_val_2881_ = lean_ctor_get(v_a_2877_, 0);
lean_inc_ref(v_val_2881_);
lean_dec_ref_known(v_a_2877_, 1);
v___x_2882_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2881_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2882_;
}
else
{
lean_object* v___x_2884_; 
lean_dec(v_a_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v_a_2875_);
v___x_2884_ = v___x_2879_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2875_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2875_);
v_a_2887_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2876_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2876_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
return v___x_2874_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_e_2861_);
v_a_2895_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2870_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2870_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2861_ = stack[0].m_obj;
uint8_t v_a_2862_ = stack[1].m_num;
lean_object* v_a_2863_ = stack[2].m_obj;
lean_object* v_a_2864_ = stack[3].m_obj;
lean_object* v_a_2865_ = stack[4].m_obj;
lean_object* v_a_2866_ = stack[5].m_obj;
lean_object* v_a_2867_ = stack[6].m_obj;
lean_object* v_a_2868_ = stack[7].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
stack->m_obj
 = v_res_2903_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2910_, uint8_t v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___x_2929_; 
lean_inc_ref(v_e_2910_);
v___x_2929_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2910_, v_a_2915_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = l_Lean_Expr_cleanupAnnotations(v_a_2930_);
v___x_2932_ = l_Lean_Expr_isApp(v___x_2931_);
if (v___x_2932_ == 0)
{
lean_dec_ref(v___x_2931_);
v___y_2920_ = v_a_2911_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
else
{
lean_object* v_arg_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v_arg_2933_ = lean_ctor_get(v___x_2931_, 1);
lean_inc_ref(v_arg_2933_);
v___x_2934_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2931_);
v___x_2935_ = l_Lean_Expr_isApp(v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_arg_2933_);
v___y_2920_ = v_a_2911_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
else
{
lean_object* v_arg_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_arg_2936_ = lean_ctor_get(v___x_2934_, 1);
lean_inc_ref(v_arg_2936_);
v___x_2937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2934_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2939_ = l_Lean_Expr_isConstOf(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_dec_ref(v___x_2937_);
lean_dec_ref(v_arg_2936_);
lean_dec_ref(v_arg_2933_);
v___y_2920_ = v_a_2911_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2937_, v_arg_2936_, v_arg_2933_, v_e_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
return v___x_2940_;
}
}
}
}
else
{
lean_dec_ref(v_e_2910_);
return v___x_2929_;
}
v___jp_2919_:
{
uint8_t v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = 0;
v___x_2928_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2910_, v___x_2927_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v___x_2928_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2910_ = stack[0].m_obj;
uint8_t v_a_2911_ = stack[1].m_num;
lean_object* v_a_2912_ = stack[2].m_obj;
lean_object* v_a_2913_ = stack[3].m_obj;
lean_object* v_a_2914_ = stack[4].m_obj;
lean_object* v_a_2915_ = stack[5].m_obj;
lean_object* v_a_2916_ = stack[6].m_obj;
lean_object* v_a_2917_ = stack[7].m_obj;
lean_object* v_res_2941_;
v_res_2941_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
stack->m_obj
 = v_res_2941_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2942_, lean_object* v_00_u03b1_2943_, lean_object* v_c_2944_, lean_object* v_inst_2945_, lean_object* v_a_2946_, lean_object* v_b_2947_, uint8_t v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2944_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; uint8_t v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_n(v_a_2957_, 2);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2957_);
if (v___x_2958_ == 0)
{
uint8_t v___x_2959_; 
lean_inc(v_a_2957_);
v___x_2959_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2957_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2943_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2945_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2946_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2975_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = l_Lean_mkApp5(v_f_2942_, v_a_2961_, v_a_2957_, v_a_2963_, v_a_2965_, v_a_2967_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
lean_dec(v_a_2965_);
lean_dec(v_a_2963_);
lean_dec(v_a_2961_);
lean_dec(v_a_2957_);
lean_dec_ref(v_f_2942_);
return v___x_2966_;
}
}
else
{
lean_dec(v_a_2963_);
lean_dec(v_a_2961_);
lean_dec(v_a_2957_);
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_f_2942_);
return v___x_2964_;
}
}
else
{
lean_dec(v_a_2961_);
lean_dec(v_a_2957_);
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_f_2942_);
return v___x_2962_;
}
}
else
{
lean_dec(v_a_2957_);
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec_ref(v_f_2942_);
return v___x_2960_;
}
}
else
{
lean_object* v___x_2976_; 
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec_ref(v_00_u03b1_2943_);
lean_dec_ref(v_f_2942_);
v___x_2976_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
return v___x_2976_;
}
}
else
{
lean_object* v___x_2977_; 
lean_dec(v_a_2957_);
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_inst_2945_);
lean_dec_ref(v_00_u03b1_2943_);
lean_dec_ref(v_f_2942_);
v___x_2977_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2946_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
return v___x_2977_;
}
}
else
{
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec_ref(v_00_u03b1_2943_);
lean_dec_ref(v_f_2942_);
return v___x_2956_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2942_ = stack[0].m_obj;
lean_object* v_00_u03b1_2943_ = stack[1].m_obj;
lean_object* v_c_2944_ = stack[2].m_obj;
lean_object* v_inst_2945_ = stack[3].m_obj;
lean_object* v_a_2946_ = stack[4].m_obj;
lean_object* v_b_2947_ = stack[5].m_obj;
uint8_t v_a_2948_ = stack[6].m_num;
lean_object* v_a_2949_ = stack[7].m_obj;
lean_object* v_a_2950_ = stack[8].m_obj;
lean_object* v_a_2951_ = stack[9].m_obj;
lean_object* v_a_2952_ = stack[10].m_obj;
lean_object* v_a_2953_ = stack[11].m_obj;
lean_object* v_a_2954_ = stack[12].m_obj;
lean_object* v_res_2978_;
v_res_2978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_2942_, v_00_u03b1_2943_, v_c_2944_, v_inst_2945_, v_a_2946_, v_b_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
stack->m_obj
 = v_res_2978_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2979_, lean_object* v_00_u03b1_2980_, lean_object* v_c_2981_, lean_object* v_a_2982_, lean_object* v_b_2983_, uint8_t v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2981_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; uint8_t v___x_2994_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc_n(v_a_2993_, 2);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = l_Lean_Expr_isBoolTrue(v_a_2993_);
if (v___x_2994_ == 0)
{
uint8_t v___x_2995_; 
lean_inc(v_a_2993_);
v___x_2995_ = l_Lean_Expr_isBoolFalse(v_a_2993_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2980_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2982_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3009_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = l_Lean_mkApp4(v_f_2979_, v_a_2997_, v_a_2993_, v_a_2999_, v_a_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_dec(v_a_2999_);
lean_dec(v_a_2997_);
lean_dec(v_a_2993_);
lean_dec_ref(v_f_2979_);
return v___x_3000_;
}
}
else
{
lean_dec(v_a_2997_);
lean_dec(v_a_2993_);
lean_dec_ref(v_b_2983_);
lean_dec_ref(v_f_2979_);
return v___x_2998_;
}
}
else
{
lean_dec(v_a_2993_);
lean_dec_ref(v_b_2983_);
lean_dec_ref(v_a_2982_);
lean_dec_ref(v_f_2979_);
return v___x_2996_;
}
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2982_);
lean_dec_ref(v_00_u03b1_2980_);
lean_dec_ref(v_f_2979_);
v___x_3010_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_3010_;
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_a_2993_);
lean_dec_ref(v_b_2983_);
lean_dec_ref(v_00_u03b1_2980_);
lean_dec_ref(v_f_2979_);
v___x_3011_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2982_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_3011_;
}
}
else
{
lean_dec_ref(v_b_2983_);
lean_dec_ref(v_a_2982_);
lean_dec_ref(v_00_u03b1_2980_);
lean_dec_ref(v_f_2979_);
return v___x_2992_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2979_ = stack[0].m_obj;
lean_object* v_00_u03b1_2980_ = stack[1].m_obj;
lean_object* v_c_2981_ = stack[2].m_obj;
lean_object* v_a_2982_ = stack[3].m_obj;
lean_object* v_b_2983_ = stack[4].m_obj;
uint8_t v_a_2984_ = stack[5].m_num;
lean_object* v_a_2985_ = stack[6].m_obj;
lean_object* v_a_2986_ = stack[7].m_obj;
lean_object* v_a_2987_ = stack[8].m_obj;
lean_object* v_a_2988_ = stack[9].m_obj;
lean_object* v_a_2989_ = stack[10].m_obj;
lean_object* v_a_2990_ = stack[11].m_obj;
lean_object* v_res_3012_;
v_res_3012_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_2979_, v_00_u03b1_2980_, v_c_2981_, v_a_2982_, v_b_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
stack->m_obj
 = v_res_3012_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_3013_, uint8_t v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; uint8_t v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; uint8_t v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___x_3059_; 
lean_inc_ref(v_e_3013_);
v___x_3059_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3013_, v_a_3018_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_Expr_cleanupAnnotations(v_a_3060_);
v___x_3062_ = l_Lean_Expr_isApp(v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3061_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_arg_3063_ = lean_ctor_get(v___x_3061_, 1);
lean_inc_ref(v_arg_3063_);
v___x_3064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3061_);
v___x_3065_ = l_Lean_Expr_isApp(v___x_3064_);
if (v___x_3065_ == 0)
{
lean_dec_ref(v___x_3064_);
lean_dec_ref(v_arg_3063_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_arg_3066_ = lean_ctor_get(v___x_3064_, 1);
lean_inc_ref(v_arg_3066_);
v___x_3067_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3064_);
v___x_3068_ = l_Lean_Expr_isApp(v___x_3067_);
if (v___x_3068_ == 0)
{
lean_dec_ref(v___x_3067_);
lean_dec_ref(v_arg_3066_);
lean_dec_ref(v_arg_3063_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_arg_3069_ = lean_ctor_get(v___x_3067_, 1);
lean_inc_ref(v_arg_3069_);
v___x_3070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3067_);
v___x_3071_ = l_Lean_Expr_isApp(v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_arg_3069_);
lean_dec_ref(v_arg_3066_);
lean_dec_ref(v_arg_3063_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_arg_3072_ = lean_ctor_get(v___x_3070_, 1);
lean_inc_ref(v_arg_3072_);
v___x_3073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3070_);
v___x_3074_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3075_ = l_Lean_Expr_isConstOf(v___x_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
uint8_t v___x_3076_; 
v___x_3076_ = l_Lean_Expr_isApp(v___x_3073_);
if (v___x_3076_ == 0)
{
lean_dec_ref(v___x_3073_);
lean_dec_ref(v_arg_3072_);
lean_dec_ref(v_arg_3069_);
lean_dec_ref(v_arg_3066_);
lean_dec_ref(v_arg_3063_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_arg_3077_ = lean_ctor_get(v___x_3073_, 1);
lean_inc_ref(v_arg_3077_);
v___x_3078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3073_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3080_ = l_Lean_Expr_isConstOf(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_dec_ref(v___x_3078_);
lean_dec_ref(v_arg_3077_);
lean_dec_ref(v_arg_3072_);
lean_dec_ref(v_arg_3069_);
lean_dec_ref(v_arg_3066_);
lean_dec_ref(v_arg_3063_);
v___y_3050_ = v_a_3014_;
v___y_3051_ = v_a_3015_;
v___y_3052_ = v_a_3016_;
v___y_3053_ = v_a_3017_;
v___y_3054_ = v_a_3018_;
v___y_3055_ = v_a_3019_;
v___y_3056_ = v_a_3020_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3081_; 
lean_dec_ref(v_e_3013_);
v___x_3081_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3078_, v_arg_3077_, v_arg_3072_, v_arg_3069_, v_arg_3066_, v_arg_3063_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3081_;
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec_ref(v_e_3013_);
v___x_3082_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3073_, v_arg_3072_, v_arg_3069_, v_arg_3066_, v_arg_3063_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3082_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_3013_);
return v___x_3059_;
}
v___jp_3022_:
{
if (v___y_3031_ == 0)
{
if (lean_obj_tag(v___y_3030_) == 4)
{
lean_object* v_declName_3032_; lean_object* v___x_3033_; 
v_declName_3032_ = lean_ctor_get(v___y_3030_, 0);
lean_inc(v_declName_3032_);
lean_dec_ref_known(v___y_3030_, 2);
v___x_3033_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3032_, v___y_3029_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; uint8_t v___x_3035_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = lean_unbox(v_a_3034_);
lean_dec(v_a_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3013_, v___y_3028_, v___y_3027_, v___y_3026_, v___y_3024_, v___y_3025_, v___y_3023_, v___y_3029_);
return v___x_3036_;
}
else
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3013_, v___y_3028_, v___y_3027_, v___y_3026_, v___y_3024_, v___y_3025_, v___y_3023_, v___y_3029_);
return v___x_3037_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_e_3013_);
v_a_3038_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3033_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3033_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v___x_3046_; 
lean_dec_ref(v___y_3030_);
v___x_3046_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3013_, v___y_3028_, v___y_3027_, v___y_3026_, v___y_3024_, v___y_3025_, v___y_3023_, v___y_3029_);
return v___x_3046_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v___y_3030_);
v___x_3047_ = l_Lean_Expr_headBeta(v_e_3013_);
v___x_3048_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3047_, v___y_3028_, v___y_3027_, v___y_3026_, v___y_3024_, v___y_3025_, v___y_3023_, v___y_3029_);
return v___x_3048_;
}
}
v___jp_3049_:
{
lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3057_ = l_Lean_Expr_getAppFn(v_e_3013_);
v___x_3058_ = l_Lean_Expr_isLambda(v___x_3057_);
if (v___x_3058_ == 0)
{
v___y_3023_ = v___y_3055_;
v___y_3024_ = v___y_3053_;
v___y_3025_ = v___y_3054_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3051_;
v___y_3028_ = v___y_3050_;
v___y_3029_ = v___y_3056_;
v___y_3030_ = v___x_3057_;
v___y_3031_ = v___x_3058_;
goto v___jp_3022_;
}
else
{
v___y_3023_ = v___y_3055_;
v___y_3024_ = v___y_3053_;
v___y_3025_ = v___y_3054_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3051_;
v___y_3028_ = v___y_3050_;
v___y_3029_ = v___y_3056_;
v___y_3030_ = v___x_3057_;
v___y_3031_ = v___y_3050_;
goto v___jp_3022_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3013_ = stack[0].m_obj;
uint8_t v_a_3014_ = stack[1].m_num;
lean_object* v_a_3015_ = stack[2].m_obj;
lean_object* v_a_3016_ = stack[3].m_obj;
lean_object* v_a_3017_ = stack[4].m_obj;
lean_object* v_a_3018_ = stack[5].m_obj;
lean_object* v_a_3019_ = stack[6].m_obj;
lean_object* v_a_3020_ = stack[7].m_obj;
lean_object* v_res_3083_;
v_res_3083_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
stack->m_obj
 = v_res_3083_;
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3088_ = lean_unsigned_to_nat(18u);
v___x_3089_ = lean_unsigned_to_nat(1913u);
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3092_ = l_mkPanicMessageWithDecl(v___x_3091_, v___x_3090_, v___x_3089_, v___x_3088_, v___x_3087_);
return v___x_3092_;
}
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3093_, uint8_t v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = l_Lean_Expr_projExpr_x21(v_e_3093_);
v___x_3103_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3102_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___y_3106_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
if (lean_obj_tag(v_e_3093_) == 11)
{
lean_object* v_typeName_3128_; lean_object* v_idx_3129_; lean_object* v_struct_3130_; size_t v___x_3131_; size_t v___x_3132_; uint8_t v___x_3133_; 
v_typeName_3128_ = lean_ctor_get(v_e_3093_, 0);
v_idx_3129_ = lean_ctor_get(v_e_3093_, 1);
v_struct_3130_ = lean_ctor_get(v_e_3093_, 2);
v___x_3131_ = lean_ptr_addr(v_struct_3130_);
v___x_3132_ = lean_ptr_addr(v_a_3104_);
v___x_3133_ = lean_usize_dec_eq(v___x_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_inc(v_idx_3129_);
lean_inc(v_typeName_3128_);
lean_dec_ref_known(v_e_3093_, 3);
v___x_3134_ = l_Lean_Expr_proj___override(v_typeName_3128_, v_idx_3129_, v_a_3104_);
v___y_3106_ = v___x_3134_;
goto v___jp_3105_;
}
else
{
lean_dec(v_a_3104_);
v___y_3106_ = v_e_3093_;
goto v___jp_3105_;
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3093_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3136_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3135_);
v___y_3106_ = v___x_3136_;
goto v___jp_3105_;
}
v___jp_3105_:
{
lean_object* v___x_3107_; 
lean_inc_ref(v___y_3106_);
v___x_3107_ = l_Lean_Meta_reduceProj_x3f(v___y_3106_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3119_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3119_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3119_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
if (lean_obj_tag(v_a_3108_) == 0)
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___y_3106_);
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___y_3106_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
else
{
lean_object* v_val_3115_; lean_object* v___x_3117_; 
lean_dec_ref(v___y_3106_);
v_val_3115_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v_a_3108_, 1);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_val_3115_);
v___x_3117_ = v___x_3110_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_val_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v___y_3106_);
v_a_3120_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3107_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3107_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3093_);
return v___x_3103_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3093_ = stack[0].m_obj;
uint8_t v_a_3094_ = stack[1].m_num;
lean_object* v_a_3095_ = stack[2].m_obj;
lean_object* v_a_3096_ = stack[3].m_obj;
lean_object* v_a_3097_ = stack[4].m_obj;
lean_object* v_a_3098_ = stack[5].m_obj;
lean_object* v_a_3099_ = stack[6].m_obj;
lean_object* v_a_3100_ = stack[7].m_obj;
lean_object* v_res_3137_;
v_res_3137_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
stack->m_obj
 = v_res_3137_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3138_, uint8_t v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
switch(lean_obj_tag(v_e_3138_))
{
case 7:
{
lean_object* v___x_3147_; 
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3139_ == 0)
{
lean_object* v___x_3148_; lean_object* v_canon_3149_; lean_object* v_cache_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_st_ref_get(v_a_3141_);
v_canon_3149_ = lean_ctor_get(v___x_3148_, 10);
lean_inc_ref(v_canon_3149_);
lean_dec(v___x_3148_);
v_cache_3150_ = lean_ctor_get(v_canon_3149_, 0);
lean_inc_ref(v_cache_3150_);
lean_dec_ref(v_canon_3149_);
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3150_, v_e_3138_);
lean_dec_ref(v_cache_3150_);
if (lean_obj_tag(v___x_3151_) == 1)
{
lean_object* v_val_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_val_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 0);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_val_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v___x_3160_; 
lean_dec(v___x_3151_);
lean_inc_ref(v_e_3138_);
v___x_3160_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3147_, v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3200_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3200_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3200_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v_canon_3166_; lean_object* v_share_3167_; lean_object* v_maxFVar_3168_; lean_object* v_proofInstInfo_3169_; lean_object* v_proofInstInfoFVar_3170_; lean_object* v_inferType_3171_; lean_object* v_getLevel_3172_; lean_object* v_congrInfo_3173_; lean_object* v_defEqI_3174_; lean_object* v_extensions_3175_; lean_object* v_issues_3176_; lean_object* v_instanceOverrides_3177_; uint8_t v_debug_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3199_; 
v___x_3165_ = lean_st_ref_take(v_a_3141_);
v_canon_3166_ = lean_ctor_get(v___x_3165_, 10);
v_share_3167_ = lean_ctor_get(v___x_3165_, 0);
v_maxFVar_3168_ = lean_ctor_get(v___x_3165_, 1);
v_proofInstInfo_3169_ = lean_ctor_get(v___x_3165_, 2);
v_proofInstInfoFVar_3170_ = lean_ctor_get(v___x_3165_, 3);
v_inferType_3171_ = lean_ctor_get(v___x_3165_, 4);
v_getLevel_3172_ = lean_ctor_get(v___x_3165_, 5);
v_congrInfo_3173_ = lean_ctor_get(v___x_3165_, 6);
v_defEqI_3174_ = lean_ctor_get(v___x_3165_, 7);
v_extensions_3175_ = lean_ctor_get(v___x_3165_, 8);
v_issues_3176_ = lean_ctor_get(v___x_3165_, 9);
v_instanceOverrides_3177_ = lean_ctor_get(v___x_3165_, 11);
v_debug_3178_ = lean_ctor_get_uint8(v___x_3165_, sizeof(void*)*12);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3180_ = v___x_3165_;
v_isShared_3181_ = v_isSharedCheck_3199_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_instanceOverrides_3177_);
lean_inc(v_canon_3166_);
lean_inc(v_issues_3176_);
lean_inc(v_extensions_3175_);
lean_inc(v_defEqI_3174_);
lean_inc(v_congrInfo_3173_);
lean_inc(v_getLevel_3172_);
lean_inc(v_inferType_3171_);
lean_inc(v_proofInstInfoFVar_3170_);
lean_inc(v_proofInstInfo_3169_);
lean_inc(v_maxFVar_3168_);
lean_inc(v_share_3167_);
lean_dec(v___x_3165_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3199_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_cache_3182_; lean_object* v_cacheInType_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3198_; 
v_cache_3182_ = lean_ctor_get(v_canon_3166_, 0);
v_cacheInType_3183_ = lean_ctor_get(v_canon_3166_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_canon_3166_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3185_ = v_canon_3166_;
v_isShared_3186_ = v_isSharedCheck_3198_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_cacheInType_3183_);
lean_inc(v_cache_3182_);
lean_dec(v_canon_3166_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3198_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
lean_inc(v_a_3161_);
v___x_3187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3182_, v_e_3138_, v_a_3161_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_cacheInType_3183_);
v___x_3189_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 10, v___x_3189_);
v___x_3191_ = v___x_3180_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_share_3167_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_maxFVar_3168_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_proofInstInfo_3169_);
lean_ctor_set(v_reuseFailAlloc_3196_, 3, v_proofInstInfoFVar_3170_);
lean_ctor_set(v_reuseFailAlloc_3196_, 4, v_inferType_3171_);
lean_ctor_set(v_reuseFailAlloc_3196_, 5, v_getLevel_3172_);
lean_ctor_set(v_reuseFailAlloc_3196_, 6, v_congrInfo_3173_);
lean_ctor_set(v_reuseFailAlloc_3196_, 7, v_defEqI_3174_);
lean_ctor_set(v_reuseFailAlloc_3196_, 8, v_extensions_3175_);
lean_ctor_set(v_reuseFailAlloc_3196_, 9, v_issues_3176_);
lean_ctor_set(v_reuseFailAlloc_3196_, 10, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3196_, 11, v_instanceOverrides_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3196_, sizeof(void*)*12, v_debug_3178_);
v___x_3191_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3192_ = lean_st_ref_put(v_a_3141_, v___x_3191_);
if (v_isShared_3164_ == 0)
{
v___x_3194_ = v___x_3163_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3161_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3160_;
}
}
}
else
{
lean_object* v___x_3201_; lean_object* v_canon_3202_; lean_object* v_cacheInType_3203_; lean_object* v___x_3204_; 
v___x_3201_ = lean_st_ref_get(v_a_3141_);
v_canon_3202_ = lean_ctor_get(v___x_3201_, 10);
lean_inc_ref(v_canon_3202_);
lean_dec(v___x_3201_);
v_cacheInType_3203_ = lean_ctor_get(v_canon_3202_, 1);
lean_inc_ref(v_cacheInType_3203_);
lean_dec_ref(v_canon_3202_);
v___x_3204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3203_, v_e_3138_);
lean_dec_ref(v_cacheInType_3203_);
if (lean_obj_tag(v___x_3204_) == 1)
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3205_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3204_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_val_3205_);
lean_dec(v___x_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set_tag(v___x_3207_, 0);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_val_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
lean_object* v___x_3213_; 
lean_dec(v___x_3204_);
lean_inc_ref(v_e_3138_);
v___x_3213_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3147_, v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3253_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3253_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3253_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v_canon_3219_; lean_object* v_share_3220_; lean_object* v_maxFVar_3221_; lean_object* v_proofInstInfo_3222_; lean_object* v_proofInstInfoFVar_3223_; lean_object* v_inferType_3224_; lean_object* v_getLevel_3225_; lean_object* v_congrInfo_3226_; lean_object* v_defEqI_3227_; lean_object* v_extensions_3228_; lean_object* v_issues_3229_; lean_object* v_instanceOverrides_3230_; uint8_t v_debug_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3252_; 
v___x_3218_ = lean_st_ref_take(v_a_3141_);
v_canon_3219_ = lean_ctor_get(v___x_3218_, 10);
v_share_3220_ = lean_ctor_get(v___x_3218_, 0);
v_maxFVar_3221_ = lean_ctor_get(v___x_3218_, 1);
v_proofInstInfo_3222_ = lean_ctor_get(v___x_3218_, 2);
v_proofInstInfoFVar_3223_ = lean_ctor_get(v___x_3218_, 3);
v_inferType_3224_ = lean_ctor_get(v___x_3218_, 4);
v_getLevel_3225_ = lean_ctor_get(v___x_3218_, 5);
v_congrInfo_3226_ = lean_ctor_get(v___x_3218_, 6);
v_defEqI_3227_ = lean_ctor_get(v___x_3218_, 7);
v_extensions_3228_ = lean_ctor_get(v___x_3218_, 8);
v_issues_3229_ = lean_ctor_get(v___x_3218_, 9);
v_instanceOverrides_3230_ = lean_ctor_get(v___x_3218_, 11);
v_debug_3231_ = lean_ctor_get_uint8(v___x_3218_, sizeof(void*)*12);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3233_ = v___x_3218_;
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_instanceOverrides_3230_);
lean_inc(v_canon_3219_);
lean_inc(v_issues_3229_);
lean_inc(v_extensions_3228_);
lean_inc(v_defEqI_3227_);
lean_inc(v_congrInfo_3226_);
lean_inc(v_getLevel_3225_);
lean_inc(v_inferType_3224_);
lean_inc(v_proofInstInfoFVar_3223_);
lean_inc(v_proofInstInfo_3222_);
lean_inc(v_maxFVar_3221_);
lean_inc(v_share_3220_);
lean_dec(v___x_3218_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_cache_3235_; lean_object* v_cacheInType_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3251_; 
v_cache_3235_ = lean_ctor_get(v_canon_3219_, 0);
v_cacheInType_3236_ = lean_ctor_get(v_canon_3219_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_canon_3219_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3238_ = v_canon_3219_;
v_isShared_3239_ = v_isSharedCheck_3251_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_cacheInType_3236_);
lean_inc(v_cache_3235_);
lean_dec(v_canon_3219_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3251_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_inc(v_a_3214_);
v___x_3240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3236_, v_e_3138_, v_a_3214_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 1, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_cache_3235_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 10, v___x_3242_);
v___x_3244_ = v___x_3233_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_share_3220_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_maxFVar_3221_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_proofInstInfo_3222_);
lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_proofInstInfoFVar_3223_);
lean_ctor_set(v_reuseFailAlloc_3249_, 4, v_inferType_3224_);
lean_ctor_set(v_reuseFailAlloc_3249_, 5, v_getLevel_3225_);
lean_ctor_set(v_reuseFailAlloc_3249_, 6, v_congrInfo_3226_);
lean_ctor_set(v_reuseFailAlloc_3249_, 7, v_defEqI_3227_);
lean_ctor_set(v_reuseFailAlloc_3249_, 8, v_extensions_3228_);
lean_ctor_set(v_reuseFailAlloc_3249_, 9, v_issues_3229_);
lean_ctor_set(v_reuseFailAlloc_3249_, 10, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3249_, 11, v_instanceOverrides_3230_);
lean_ctor_set_uint8(v_reuseFailAlloc_3249_, sizeof(void*)*12, v_debug_3231_);
v___x_3244_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3245_ = lean_st_ref_put(v_a_3141_, v___x_3244_);
if (v_isShared_3217_ == 0)
{
v___x_3247_ = v___x_3216_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3214_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3213_;
}
}
}
}
case 6:
{
if (v_a_3139_ == 0)
{
lean_object* v___x_3254_; lean_object* v_canon_3255_; lean_object* v_cache_3256_; lean_object* v___x_3257_; 
v___x_3254_ = lean_st_ref_get(v_a_3141_);
v_canon_3255_ = lean_ctor_get(v___x_3254_, 10);
lean_inc_ref(v_canon_3255_);
lean_dec(v___x_3254_);
v_cache_3256_ = lean_ctor_get(v_canon_3255_, 0);
lean_inc_ref(v_cache_3256_);
lean_dec_ref(v_canon_3255_);
v___x_3257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3256_, v_e_3138_);
lean_dec_ref(v_cache_3256_);
if (lean_obj_tag(v___x_3257_) == 1)
{
lean_object* v_val_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_val_3258_);
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
lean_ctor_set_tag(v___x_3260_, 0);
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_val_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
else
{
lean_object* v___x_3266_; 
lean_dec(v___x_3257_);
lean_inc_ref(v_e_3138_);
v___x_3266_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3306_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3306_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3306_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v_canon_3272_; lean_object* v_share_3273_; lean_object* v_maxFVar_3274_; lean_object* v_proofInstInfo_3275_; lean_object* v_proofInstInfoFVar_3276_; lean_object* v_inferType_3277_; lean_object* v_getLevel_3278_; lean_object* v_congrInfo_3279_; lean_object* v_defEqI_3280_; lean_object* v_extensions_3281_; lean_object* v_issues_3282_; lean_object* v_instanceOverrides_3283_; uint8_t v_debug_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3305_; 
v___x_3271_ = lean_st_ref_take(v_a_3141_);
v_canon_3272_ = lean_ctor_get(v___x_3271_, 10);
v_share_3273_ = lean_ctor_get(v___x_3271_, 0);
v_maxFVar_3274_ = lean_ctor_get(v___x_3271_, 1);
v_proofInstInfo_3275_ = lean_ctor_get(v___x_3271_, 2);
v_proofInstInfoFVar_3276_ = lean_ctor_get(v___x_3271_, 3);
v_inferType_3277_ = lean_ctor_get(v___x_3271_, 4);
v_getLevel_3278_ = lean_ctor_get(v___x_3271_, 5);
v_congrInfo_3279_ = lean_ctor_get(v___x_3271_, 6);
v_defEqI_3280_ = lean_ctor_get(v___x_3271_, 7);
v_extensions_3281_ = lean_ctor_get(v___x_3271_, 8);
v_issues_3282_ = lean_ctor_get(v___x_3271_, 9);
v_instanceOverrides_3283_ = lean_ctor_get(v___x_3271_, 11);
v_debug_3284_ = lean_ctor_get_uint8(v___x_3271_, sizeof(void*)*12);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3286_ = v___x_3271_;
v_isShared_3287_ = v_isSharedCheck_3305_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_instanceOverrides_3283_);
lean_inc(v_canon_3272_);
lean_inc(v_issues_3282_);
lean_inc(v_extensions_3281_);
lean_inc(v_defEqI_3280_);
lean_inc(v_congrInfo_3279_);
lean_inc(v_getLevel_3278_);
lean_inc(v_inferType_3277_);
lean_inc(v_proofInstInfoFVar_3276_);
lean_inc(v_proofInstInfo_3275_);
lean_inc(v_maxFVar_3274_);
lean_inc(v_share_3273_);
lean_dec(v___x_3271_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3305_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_cache_3288_; lean_object* v_cacheInType_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3304_; 
v_cache_3288_ = lean_ctor_get(v_canon_3272_, 0);
v_cacheInType_3289_ = lean_ctor_get(v_canon_3272_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_canon_3272_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3291_ = v_canon_3272_;
v_isShared_3292_ = v_isSharedCheck_3304_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_cacheInType_3289_);
lean_inc(v_cache_3288_);
lean_dec(v_canon_3272_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3304_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
lean_inc(v_a_3267_);
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3288_, v_e_3138_, v_a_3267_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_cacheInType_3289_);
v___x_3295_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 10, v___x_3295_);
v___x_3297_ = v___x_3286_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_share_3273_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_maxFVar_3274_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_proofInstInfo_3275_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_proofInstInfoFVar_3276_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_inferType_3277_);
lean_ctor_set(v_reuseFailAlloc_3302_, 5, v_getLevel_3278_);
lean_ctor_set(v_reuseFailAlloc_3302_, 6, v_congrInfo_3279_);
lean_ctor_set(v_reuseFailAlloc_3302_, 7, v_defEqI_3280_);
lean_ctor_set(v_reuseFailAlloc_3302_, 8, v_extensions_3281_);
lean_ctor_set(v_reuseFailAlloc_3302_, 9, v_issues_3282_);
lean_ctor_set(v_reuseFailAlloc_3302_, 10, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3302_, 11, v_instanceOverrides_3283_);
lean_ctor_set_uint8(v_reuseFailAlloc_3302_, sizeof(void*)*12, v_debug_3284_);
v___x_3297_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = lean_st_ref_put(v_a_3141_, v___x_3297_);
if (v_isShared_3270_ == 0)
{
v___x_3300_ = v___x_3269_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3267_);
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
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3266_;
}
}
}
else
{
lean_object* v___x_3307_; lean_object* v_canon_3308_; lean_object* v_cacheInType_3309_; lean_object* v___x_3310_; 
v___x_3307_ = lean_st_ref_get(v_a_3141_);
v_canon_3308_ = lean_ctor_get(v___x_3307_, 10);
lean_inc_ref(v_canon_3308_);
lean_dec(v___x_3307_);
v_cacheInType_3309_ = lean_ctor_get(v_canon_3308_, 1);
lean_inc_ref(v_cacheInType_3309_);
lean_dec_ref(v_canon_3308_);
v___x_3310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3309_, v_e_3138_);
lean_dec_ref(v_cacheInType_3309_);
if (lean_obj_tag(v___x_3310_) == 1)
{
lean_object* v_val_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_val_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 0);
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_val_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v___x_3319_; 
lean_dec(v___x_3310_);
lean_inc_ref(v_e_3138_);
v___x_3319_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3359_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3359_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3359_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v_canon_3325_; lean_object* v_share_3326_; lean_object* v_maxFVar_3327_; lean_object* v_proofInstInfo_3328_; lean_object* v_proofInstInfoFVar_3329_; lean_object* v_inferType_3330_; lean_object* v_getLevel_3331_; lean_object* v_congrInfo_3332_; lean_object* v_defEqI_3333_; lean_object* v_extensions_3334_; lean_object* v_issues_3335_; lean_object* v_instanceOverrides_3336_; uint8_t v_debug_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3358_; 
v___x_3324_ = lean_st_ref_take(v_a_3141_);
v_canon_3325_ = lean_ctor_get(v___x_3324_, 10);
v_share_3326_ = lean_ctor_get(v___x_3324_, 0);
v_maxFVar_3327_ = lean_ctor_get(v___x_3324_, 1);
v_proofInstInfo_3328_ = lean_ctor_get(v___x_3324_, 2);
v_proofInstInfoFVar_3329_ = lean_ctor_get(v___x_3324_, 3);
v_inferType_3330_ = lean_ctor_get(v___x_3324_, 4);
v_getLevel_3331_ = lean_ctor_get(v___x_3324_, 5);
v_congrInfo_3332_ = lean_ctor_get(v___x_3324_, 6);
v_defEqI_3333_ = lean_ctor_get(v___x_3324_, 7);
v_extensions_3334_ = lean_ctor_get(v___x_3324_, 8);
v_issues_3335_ = lean_ctor_get(v___x_3324_, 9);
v_instanceOverrides_3336_ = lean_ctor_get(v___x_3324_, 11);
v_debug_3337_ = lean_ctor_get_uint8(v___x_3324_, sizeof(void*)*12);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3339_ = v___x_3324_;
v_isShared_3340_ = v_isSharedCheck_3358_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_instanceOverrides_3336_);
lean_inc(v_canon_3325_);
lean_inc(v_issues_3335_);
lean_inc(v_extensions_3334_);
lean_inc(v_defEqI_3333_);
lean_inc(v_congrInfo_3332_);
lean_inc(v_getLevel_3331_);
lean_inc(v_inferType_3330_);
lean_inc(v_proofInstInfoFVar_3329_);
lean_inc(v_proofInstInfo_3328_);
lean_inc(v_maxFVar_3327_);
lean_inc(v_share_3326_);
lean_dec(v___x_3324_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3358_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_cache_3341_; lean_object* v_cacheInType_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3357_; 
v_cache_3341_ = lean_ctor_get(v_canon_3325_, 0);
v_cacheInType_3342_ = lean_ctor_get(v_canon_3325_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_canon_3325_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3344_ = v_canon_3325_;
v_isShared_3345_ = v_isSharedCheck_3357_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_cacheInType_3342_);
lean_inc(v_cache_3341_);
lean_dec(v_canon_3325_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3357_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_inc(v_a_3320_);
v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3342_, v_e_3138_, v_a_3320_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v___x_3346_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_cache_3341_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 10, v___x_3348_);
v___x_3350_ = v___x_3339_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_share_3326_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_maxFVar_3327_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_proofInstInfo_3328_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_proofInstInfoFVar_3329_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_inferType_3330_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v_getLevel_3331_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v_congrInfo_3332_);
lean_ctor_set(v_reuseFailAlloc_3355_, 7, v_defEqI_3333_);
lean_ctor_set(v_reuseFailAlloc_3355_, 8, v_extensions_3334_);
lean_ctor_set(v_reuseFailAlloc_3355_, 9, v_issues_3335_);
lean_ctor_set(v_reuseFailAlloc_3355_, 10, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3355_, 11, v_instanceOverrides_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*12, v_debug_3337_);
v___x_3350_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_st_ref_put(v_a_3141_, v___x_3350_);
if (v_isShared_3323_ == 0)
{
v___x_3353_ = v___x_3322_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3320_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3319_;
}
}
}
}
case 8:
{
lean_object* v___x_3360_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3139_ == 0)
{
lean_object* v___x_3361_; lean_object* v_canon_3362_; lean_object* v_cache_3363_; lean_object* v___x_3364_; 
v___x_3361_ = lean_st_ref_get(v_a_3141_);
v_canon_3362_ = lean_ctor_get(v___x_3361_, 10);
lean_inc_ref(v_canon_3362_);
lean_dec(v___x_3361_);
v_cache_3363_ = lean_ctor_get(v_canon_3362_, 0);
lean_inc_ref(v_cache_3363_);
lean_dec_ref(v_canon_3362_);
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3363_, v_e_3138_);
lean_dec_ref(v_cache_3363_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref_known(v_e_3138_, 4);
v_val_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_val_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set_tag(v___x_3367_, 0);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_val_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v___x_3373_; 
lean_dec(v___x_3364_);
lean_inc_ref(v_e_3138_);
v___x_3373_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3360_, v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3413_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3413_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3413_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v_canon_3379_; lean_object* v_share_3380_; lean_object* v_maxFVar_3381_; lean_object* v_proofInstInfo_3382_; lean_object* v_proofInstInfoFVar_3383_; lean_object* v_inferType_3384_; lean_object* v_getLevel_3385_; lean_object* v_congrInfo_3386_; lean_object* v_defEqI_3387_; lean_object* v_extensions_3388_; lean_object* v_issues_3389_; lean_object* v_instanceOverrides_3390_; uint8_t v_debug_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3412_; 
v___x_3378_ = lean_st_ref_take(v_a_3141_);
v_canon_3379_ = lean_ctor_get(v___x_3378_, 10);
v_share_3380_ = lean_ctor_get(v___x_3378_, 0);
v_maxFVar_3381_ = lean_ctor_get(v___x_3378_, 1);
v_proofInstInfo_3382_ = lean_ctor_get(v___x_3378_, 2);
v_proofInstInfoFVar_3383_ = lean_ctor_get(v___x_3378_, 3);
v_inferType_3384_ = lean_ctor_get(v___x_3378_, 4);
v_getLevel_3385_ = lean_ctor_get(v___x_3378_, 5);
v_congrInfo_3386_ = lean_ctor_get(v___x_3378_, 6);
v_defEqI_3387_ = lean_ctor_get(v___x_3378_, 7);
v_extensions_3388_ = lean_ctor_get(v___x_3378_, 8);
v_issues_3389_ = lean_ctor_get(v___x_3378_, 9);
v_instanceOverrides_3390_ = lean_ctor_get(v___x_3378_, 11);
v_debug_3391_ = lean_ctor_get_uint8(v___x_3378_, sizeof(void*)*12);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3393_ = v___x_3378_;
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_instanceOverrides_3390_);
lean_inc(v_canon_3379_);
lean_inc(v_issues_3389_);
lean_inc(v_extensions_3388_);
lean_inc(v_defEqI_3387_);
lean_inc(v_congrInfo_3386_);
lean_inc(v_getLevel_3385_);
lean_inc(v_inferType_3384_);
lean_inc(v_proofInstInfoFVar_3383_);
lean_inc(v_proofInstInfo_3382_);
lean_inc(v_maxFVar_3381_);
lean_inc(v_share_3380_);
lean_dec(v___x_3378_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_cache_3395_; lean_object* v_cacheInType_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3411_; 
v_cache_3395_ = lean_ctor_get(v_canon_3379_, 0);
v_cacheInType_3396_ = lean_ctor_get(v_canon_3379_, 1);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_canon_3379_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3398_ = v_canon_3379_;
v_isShared_3399_ = v_isSharedCheck_3411_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_cacheInType_3396_);
lean_inc(v_cache_3395_);
lean_dec(v_canon_3379_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3411_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
lean_inc(v_a_3374_);
v___x_3400_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3395_, v_e_3138_, v_a_3374_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3400_);
v___x_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_cacheInType_3396_);
v___x_3402_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 10, v___x_3402_);
v___x_3404_ = v___x_3393_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_share_3380_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_maxFVar_3381_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_proofInstInfo_3382_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_proofInstInfoFVar_3383_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_inferType_3384_);
lean_ctor_set(v_reuseFailAlloc_3409_, 5, v_getLevel_3385_);
lean_ctor_set(v_reuseFailAlloc_3409_, 6, v_congrInfo_3386_);
lean_ctor_set(v_reuseFailAlloc_3409_, 7, v_defEqI_3387_);
lean_ctor_set(v_reuseFailAlloc_3409_, 8, v_extensions_3388_);
lean_ctor_set(v_reuseFailAlloc_3409_, 9, v_issues_3389_);
lean_ctor_set(v_reuseFailAlloc_3409_, 10, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3409_, 11, v_instanceOverrides_3390_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, sizeof(void*)*12, v_debug_3391_);
v___x_3404_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = lean_st_ref_put(v_a_3141_, v___x_3404_);
if (v_isShared_3377_ == 0)
{
v___x_3407_ = v___x_3376_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3374_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 4);
return v___x_3373_;
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v_canon_3415_; lean_object* v_cacheInType_3416_; lean_object* v___x_3417_; 
v___x_3414_ = lean_st_ref_get(v_a_3141_);
v_canon_3415_ = lean_ctor_get(v___x_3414_, 10);
lean_inc_ref(v_canon_3415_);
lean_dec(v___x_3414_);
v_cacheInType_3416_ = lean_ctor_get(v_canon_3415_, 1);
lean_inc_ref(v_cacheInType_3416_);
lean_dec_ref(v_canon_3415_);
v___x_3417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3416_, v_e_3138_);
lean_dec_ref(v_cacheInType_3416_);
if (lean_obj_tag(v___x_3417_) == 1)
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref_known(v_e_3138_, 4);
v_val_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_val_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set_tag(v___x_3420_, 0);
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_val_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
lean_object* v___x_3426_; 
lean_dec(v___x_3417_);
lean_inc_ref(v_e_3138_);
v___x_3426_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3360_, v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3466_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3466_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3466_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v_canon_3432_; lean_object* v_share_3433_; lean_object* v_maxFVar_3434_; lean_object* v_proofInstInfo_3435_; lean_object* v_proofInstInfoFVar_3436_; lean_object* v_inferType_3437_; lean_object* v_getLevel_3438_; lean_object* v_congrInfo_3439_; lean_object* v_defEqI_3440_; lean_object* v_extensions_3441_; lean_object* v_issues_3442_; lean_object* v_instanceOverrides_3443_; uint8_t v_debug_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3465_; 
v___x_3431_ = lean_st_ref_take(v_a_3141_);
v_canon_3432_ = lean_ctor_get(v___x_3431_, 10);
v_share_3433_ = lean_ctor_get(v___x_3431_, 0);
v_maxFVar_3434_ = lean_ctor_get(v___x_3431_, 1);
v_proofInstInfo_3435_ = lean_ctor_get(v___x_3431_, 2);
v_proofInstInfoFVar_3436_ = lean_ctor_get(v___x_3431_, 3);
v_inferType_3437_ = lean_ctor_get(v___x_3431_, 4);
v_getLevel_3438_ = lean_ctor_get(v___x_3431_, 5);
v_congrInfo_3439_ = lean_ctor_get(v___x_3431_, 6);
v_defEqI_3440_ = lean_ctor_get(v___x_3431_, 7);
v_extensions_3441_ = lean_ctor_get(v___x_3431_, 8);
v_issues_3442_ = lean_ctor_get(v___x_3431_, 9);
v_instanceOverrides_3443_ = lean_ctor_get(v___x_3431_, 11);
v_debug_3444_ = lean_ctor_get_uint8(v___x_3431_, sizeof(void*)*12);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3446_ = v___x_3431_;
v_isShared_3447_ = v_isSharedCheck_3465_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_instanceOverrides_3443_);
lean_inc(v_canon_3432_);
lean_inc(v_issues_3442_);
lean_inc(v_extensions_3441_);
lean_inc(v_defEqI_3440_);
lean_inc(v_congrInfo_3439_);
lean_inc(v_getLevel_3438_);
lean_inc(v_inferType_3437_);
lean_inc(v_proofInstInfoFVar_3436_);
lean_inc(v_proofInstInfo_3435_);
lean_inc(v_maxFVar_3434_);
lean_inc(v_share_3433_);
lean_dec(v___x_3431_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3465_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_cache_3448_; lean_object* v_cacheInType_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3464_; 
v_cache_3448_ = lean_ctor_get(v_canon_3432_, 0);
v_cacheInType_3449_ = lean_ctor_get(v_canon_3432_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_canon_3432_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3451_ = v_canon_3432_;
v_isShared_3452_ = v_isSharedCheck_3464_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_cacheInType_3449_);
lean_inc(v_cache_3448_);
lean_dec(v_canon_3432_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3464_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_inc(v_a_3427_);
v___x_3453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3449_, v_e_3138_, v_a_3427_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___x_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_cache_3448_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 10, v___x_3455_);
v___x_3457_ = v___x_3446_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_share_3433_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_maxFVar_3434_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_proofInstInfo_3435_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_proofInstInfoFVar_3436_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_inferType_3437_);
lean_ctor_set(v_reuseFailAlloc_3462_, 5, v_getLevel_3438_);
lean_ctor_set(v_reuseFailAlloc_3462_, 6, v_congrInfo_3439_);
lean_ctor_set(v_reuseFailAlloc_3462_, 7, v_defEqI_3440_);
lean_ctor_set(v_reuseFailAlloc_3462_, 8, v_extensions_3441_);
lean_ctor_set(v_reuseFailAlloc_3462_, 9, v_issues_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 10, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3462_, 11, v_instanceOverrides_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3462_, sizeof(void*)*12, v_debug_3444_);
v___x_3457_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = lean_st_ref_put(v_a_3141_, v___x_3457_);
if (v_isShared_3430_ == 0)
{
v___x_3460_ = v___x_3429_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3427_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 4);
return v___x_3426_;
}
}
}
}
case 5:
{
if (v_a_3139_ == 0)
{
lean_object* v___x_3467_; lean_object* v_canon_3468_; lean_object* v_cache_3469_; lean_object* v___x_3470_; 
v___x_3467_ = lean_st_ref_get(v_a_3141_);
v_canon_3468_ = lean_ctor_get(v___x_3467_, 10);
lean_inc_ref(v_canon_3468_);
lean_dec(v___x_3467_);
v_cache_3469_ = lean_ctor_get(v_canon_3468_, 0);
lean_inc_ref(v_cache_3469_);
lean_dec_ref(v_canon_3468_);
v___x_3470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3469_, v_e_3138_);
lean_dec_ref(v_cache_3469_);
if (lean_obj_tag(v___x_3470_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref_known(v_e_3138_, 2);
v_val_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_val_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 0);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_val_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
else
{
lean_object* v___x_3479_; 
lean_dec(v___x_3470_);
lean_inc_ref(v_e_3138_);
v___x_3479_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3519_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3519_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3519_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v_canon_3485_; lean_object* v_share_3486_; lean_object* v_maxFVar_3487_; lean_object* v_proofInstInfo_3488_; lean_object* v_proofInstInfoFVar_3489_; lean_object* v_inferType_3490_; lean_object* v_getLevel_3491_; lean_object* v_congrInfo_3492_; lean_object* v_defEqI_3493_; lean_object* v_extensions_3494_; lean_object* v_issues_3495_; lean_object* v_instanceOverrides_3496_; uint8_t v_debug_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3518_; 
v___x_3484_ = lean_st_ref_take(v_a_3141_);
v_canon_3485_ = lean_ctor_get(v___x_3484_, 10);
v_share_3486_ = lean_ctor_get(v___x_3484_, 0);
v_maxFVar_3487_ = lean_ctor_get(v___x_3484_, 1);
v_proofInstInfo_3488_ = lean_ctor_get(v___x_3484_, 2);
v_proofInstInfoFVar_3489_ = lean_ctor_get(v___x_3484_, 3);
v_inferType_3490_ = lean_ctor_get(v___x_3484_, 4);
v_getLevel_3491_ = lean_ctor_get(v___x_3484_, 5);
v_congrInfo_3492_ = lean_ctor_get(v___x_3484_, 6);
v_defEqI_3493_ = lean_ctor_get(v___x_3484_, 7);
v_extensions_3494_ = lean_ctor_get(v___x_3484_, 8);
v_issues_3495_ = lean_ctor_get(v___x_3484_, 9);
v_instanceOverrides_3496_ = lean_ctor_get(v___x_3484_, 11);
v_debug_3497_ = lean_ctor_get_uint8(v___x_3484_, sizeof(void*)*12);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3499_ = v___x_3484_;
v_isShared_3500_ = v_isSharedCheck_3518_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_instanceOverrides_3496_);
lean_inc(v_canon_3485_);
lean_inc(v_issues_3495_);
lean_inc(v_extensions_3494_);
lean_inc(v_defEqI_3493_);
lean_inc(v_congrInfo_3492_);
lean_inc(v_getLevel_3491_);
lean_inc(v_inferType_3490_);
lean_inc(v_proofInstInfoFVar_3489_);
lean_inc(v_proofInstInfo_3488_);
lean_inc(v_maxFVar_3487_);
lean_inc(v_share_3486_);
lean_dec(v___x_3484_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3518_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_cache_3501_; lean_object* v_cacheInType_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3517_; 
v_cache_3501_ = lean_ctor_get(v_canon_3485_, 0);
v_cacheInType_3502_ = lean_ctor_get(v_canon_3485_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_canon_3485_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3504_ = v_canon_3485_;
v_isShared_3505_ = v_isSharedCheck_3517_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_cacheInType_3502_);
lean_inc(v_cache_3501_);
lean_dec(v_canon_3485_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3517_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_inc(v_a_3480_);
v___x_3506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3501_, v_e_3138_, v_a_3480_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_cacheInType_3502_);
v___x_3508_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 10, v___x_3508_);
v___x_3510_ = v___x_3499_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_share_3486_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_maxFVar_3487_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_proofInstInfo_3488_);
lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_proofInstInfoFVar_3489_);
lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_inferType_3490_);
lean_ctor_set(v_reuseFailAlloc_3515_, 5, v_getLevel_3491_);
lean_ctor_set(v_reuseFailAlloc_3515_, 6, v_congrInfo_3492_);
lean_ctor_set(v_reuseFailAlloc_3515_, 7, v_defEqI_3493_);
lean_ctor_set(v_reuseFailAlloc_3515_, 8, v_extensions_3494_);
lean_ctor_set(v_reuseFailAlloc_3515_, 9, v_issues_3495_);
lean_ctor_set(v_reuseFailAlloc_3515_, 10, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3515_, 11, v_instanceOverrides_3496_);
lean_ctor_set_uint8(v_reuseFailAlloc_3515_, sizeof(void*)*12, v_debug_3497_);
v___x_3510_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_st_ref_put(v_a_3141_, v___x_3510_);
if (v_isShared_3483_ == 0)
{
v___x_3513_ = v___x_3482_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3480_);
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
}
else
{
lean_dec_ref_known(v_e_3138_, 2);
return v___x_3479_;
}
}
}
else
{
lean_object* v___x_3520_; lean_object* v_canon_3521_; lean_object* v_cacheInType_3522_; lean_object* v___x_3523_; 
v___x_3520_ = lean_st_ref_get(v_a_3141_);
v_canon_3521_ = lean_ctor_get(v___x_3520_, 10);
lean_inc_ref(v_canon_3521_);
lean_dec(v___x_3520_);
v_cacheInType_3522_ = lean_ctor_get(v_canon_3521_, 1);
lean_inc_ref(v_cacheInType_3522_);
lean_dec_ref(v_canon_3521_);
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3522_, v_e_3138_);
lean_dec_ref(v_cacheInType_3522_);
if (lean_obj_tag(v___x_3523_) == 1)
{
lean_object* v_val_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref_known(v_e_3138_, 2);
v_val_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_val_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 0);
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_val_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
else
{
lean_object* v___x_3532_; 
lean_dec(v___x_3523_);
lean_inc_ref(v_e_3138_);
v___x_3532_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3572_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3572_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3572_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v_canon_3538_; lean_object* v_share_3539_; lean_object* v_maxFVar_3540_; lean_object* v_proofInstInfo_3541_; lean_object* v_proofInstInfoFVar_3542_; lean_object* v_inferType_3543_; lean_object* v_getLevel_3544_; lean_object* v_congrInfo_3545_; lean_object* v_defEqI_3546_; lean_object* v_extensions_3547_; lean_object* v_issues_3548_; lean_object* v_instanceOverrides_3549_; uint8_t v_debug_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3571_; 
v___x_3537_ = lean_st_ref_take(v_a_3141_);
v_canon_3538_ = lean_ctor_get(v___x_3537_, 10);
v_share_3539_ = lean_ctor_get(v___x_3537_, 0);
v_maxFVar_3540_ = lean_ctor_get(v___x_3537_, 1);
v_proofInstInfo_3541_ = lean_ctor_get(v___x_3537_, 2);
v_proofInstInfoFVar_3542_ = lean_ctor_get(v___x_3537_, 3);
v_inferType_3543_ = lean_ctor_get(v___x_3537_, 4);
v_getLevel_3544_ = lean_ctor_get(v___x_3537_, 5);
v_congrInfo_3545_ = lean_ctor_get(v___x_3537_, 6);
v_defEqI_3546_ = lean_ctor_get(v___x_3537_, 7);
v_extensions_3547_ = lean_ctor_get(v___x_3537_, 8);
v_issues_3548_ = lean_ctor_get(v___x_3537_, 9);
v_instanceOverrides_3549_ = lean_ctor_get(v___x_3537_, 11);
v_debug_3550_ = lean_ctor_get_uint8(v___x_3537_, sizeof(void*)*12);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3552_ = v___x_3537_;
v_isShared_3553_ = v_isSharedCheck_3571_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_instanceOverrides_3549_);
lean_inc(v_canon_3538_);
lean_inc(v_issues_3548_);
lean_inc(v_extensions_3547_);
lean_inc(v_defEqI_3546_);
lean_inc(v_congrInfo_3545_);
lean_inc(v_getLevel_3544_);
lean_inc(v_inferType_3543_);
lean_inc(v_proofInstInfoFVar_3542_);
lean_inc(v_proofInstInfo_3541_);
lean_inc(v_maxFVar_3540_);
lean_inc(v_share_3539_);
lean_dec(v___x_3537_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3571_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v_cache_3554_; lean_object* v_cacheInType_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3570_; 
v_cache_3554_ = lean_ctor_get(v_canon_3538_, 0);
v_cacheInType_3555_ = lean_ctor_get(v_canon_3538_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_canon_3538_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3557_ = v_canon_3538_;
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_cacheInType_3555_);
lean_inc(v_cache_3554_);
lean_dec(v_canon_3538_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_inc(v_a_3533_);
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3555_, v_e_3138_, v_a_3533_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3559_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_cache_3554_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 10, v___x_3561_);
v___x_3563_ = v___x_3552_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_share_3539_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_maxFVar_3540_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_proofInstInfo_3541_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_proofInstInfoFVar_3542_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_inferType_3543_);
lean_ctor_set(v_reuseFailAlloc_3568_, 5, v_getLevel_3544_);
lean_ctor_set(v_reuseFailAlloc_3568_, 6, v_congrInfo_3545_);
lean_ctor_set(v_reuseFailAlloc_3568_, 7, v_defEqI_3546_);
lean_ctor_set(v_reuseFailAlloc_3568_, 8, v_extensions_3547_);
lean_ctor_set(v_reuseFailAlloc_3568_, 9, v_issues_3548_);
lean_ctor_set(v_reuseFailAlloc_3568_, 10, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3568_, 11, v_instanceOverrides_3549_);
lean_ctor_set_uint8(v_reuseFailAlloc_3568_, sizeof(void*)*12, v_debug_3550_);
v___x_3563_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_st_ref_put(v_a_3141_, v___x_3563_);
if (v_isShared_3536_ == 0)
{
v___x_3566_ = v___x_3535_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3533_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 2);
return v___x_3532_;
}
}
}
}
case 11:
{
if (v_a_3139_ == 0)
{
lean_object* v___x_3573_; lean_object* v_canon_3574_; lean_object* v_cache_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_st_ref_get(v_a_3141_);
v_canon_3574_ = lean_ctor_get(v___x_3573_, 10);
lean_inc_ref(v_canon_3574_);
lean_dec(v___x_3573_);
v_cache_3575_ = lean_ctor_get(v_canon_3574_, 0);
lean_inc_ref(v_cache_3575_);
lean_dec_ref(v_canon_3574_);
v___x_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3575_, v_e_3138_);
lean_dec_ref(v_cache_3575_);
if (lean_obj_tag(v___x_3576_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_val_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set_tag(v___x_3579_, 0);
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_val_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
else
{
lean_object* v___x_3585_; 
lean_dec(v___x_3576_);
lean_inc_ref(v_e_3138_);
v___x_3585_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3625_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3625_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3625_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v_canon_3591_; lean_object* v_share_3592_; lean_object* v_maxFVar_3593_; lean_object* v_proofInstInfo_3594_; lean_object* v_proofInstInfoFVar_3595_; lean_object* v_inferType_3596_; lean_object* v_getLevel_3597_; lean_object* v_congrInfo_3598_; lean_object* v_defEqI_3599_; lean_object* v_extensions_3600_; lean_object* v_issues_3601_; lean_object* v_instanceOverrides_3602_; uint8_t v_debug_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3624_; 
v___x_3590_ = lean_st_ref_take(v_a_3141_);
v_canon_3591_ = lean_ctor_get(v___x_3590_, 10);
v_share_3592_ = lean_ctor_get(v___x_3590_, 0);
v_maxFVar_3593_ = lean_ctor_get(v___x_3590_, 1);
v_proofInstInfo_3594_ = lean_ctor_get(v___x_3590_, 2);
v_proofInstInfoFVar_3595_ = lean_ctor_get(v___x_3590_, 3);
v_inferType_3596_ = lean_ctor_get(v___x_3590_, 4);
v_getLevel_3597_ = lean_ctor_get(v___x_3590_, 5);
v_congrInfo_3598_ = lean_ctor_get(v___x_3590_, 6);
v_defEqI_3599_ = lean_ctor_get(v___x_3590_, 7);
v_extensions_3600_ = lean_ctor_get(v___x_3590_, 8);
v_issues_3601_ = lean_ctor_get(v___x_3590_, 9);
v_instanceOverrides_3602_ = lean_ctor_get(v___x_3590_, 11);
v_debug_3603_ = lean_ctor_get_uint8(v___x_3590_, sizeof(void*)*12);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3605_ = v___x_3590_;
v_isShared_3606_ = v_isSharedCheck_3624_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_instanceOverrides_3602_);
lean_inc(v_canon_3591_);
lean_inc(v_issues_3601_);
lean_inc(v_extensions_3600_);
lean_inc(v_defEqI_3599_);
lean_inc(v_congrInfo_3598_);
lean_inc(v_getLevel_3597_);
lean_inc(v_inferType_3596_);
lean_inc(v_proofInstInfoFVar_3595_);
lean_inc(v_proofInstInfo_3594_);
lean_inc(v_maxFVar_3593_);
lean_inc(v_share_3592_);
lean_dec(v___x_3590_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3624_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v_cache_3607_; lean_object* v_cacheInType_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3623_; 
v_cache_3607_ = lean_ctor_get(v_canon_3591_, 0);
v_cacheInType_3608_ = lean_ctor_get(v_canon_3591_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_canon_3591_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3610_ = v_canon_3591_;
v_isShared_3611_ = v_isSharedCheck_3623_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_cacheInType_3608_);
lean_inc(v_cache_3607_);
lean_dec(v_canon_3591_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3623_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_inc(v_a_3586_);
v___x_3612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3607_, v_e_3138_, v_a_3586_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3612_);
v___x_3614_ = v___x_3610_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_cacheInType_3608_);
v___x_3614_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 10, v___x_3614_);
v___x_3616_ = v___x_3605_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_share_3592_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_maxFVar_3593_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_proofInstInfo_3594_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_proofInstInfoFVar_3595_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_inferType_3596_);
lean_ctor_set(v_reuseFailAlloc_3621_, 5, v_getLevel_3597_);
lean_ctor_set(v_reuseFailAlloc_3621_, 6, v_congrInfo_3598_);
lean_ctor_set(v_reuseFailAlloc_3621_, 7, v_defEqI_3599_);
lean_ctor_set(v_reuseFailAlloc_3621_, 8, v_extensions_3600_);
lean_ctor_set(v_reuseFailAlloc_3621_, 9, v_issues_3601_);
lean_ctor_set(v_reuseFailAlloc_3621_, 10, v___x_3614_);
lean_ctor_set(v_reuseFailAlloc_3621_, 11, v_instanceOverrides_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3621_, sizeof(void*)*12, v_debug_3603_);
v___x_3616_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_st_ref_put(v_a_3141_, v___x_3616_);
if (v_isShared_3589_ == 0)
{
v___x_3619_ = v___x_3588_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3586_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3585_;
}
}
}
else
{
lean_object* v___x_3626_; lean_object* v_canon_3627_; lean_object* v_cacheInType_3628_; lean_object* v___x_3629_; 
v___x_3626_ = lean_st_ref_get(v_a_3141_);
v_canon_3627_ = lean_ctor_get(v___x_3626_, 10);
lean_inc_ref(v_canon_3627_);
lean_dec(v___x_3626_);
v_cacheInType_3628_ = lean_ctor_get(v_canon_3627_, 1);
lean_inc_ref(v_cacheInType_3628_);
lean_dec_ref(v_canon_3627_);
v___x_3629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3628_, v_e_3138_);
lean_dec_ref(v_cacheInType_3628_);
if (lean_obj_tag(v___x_3629_) == 1)
{
lean_object* v_val_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref_known(v_e_3138_, 3);
v_val_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_val_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 0);
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_val_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v___x_3638_; 
lean_dec(v___x_3629_);
lean_inc_ref(v_e_3138_);
v___x_3638_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3678_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3678_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3678_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v_canon_3644_; lean_object* v_share_3645_; lean_object* v_maxFVar_3646_; lean_object* v_proofInstInfo_3647_; lean_object* v_proofInstInfoFVar_3648_; lean_object* v_inferType_3649_; lean_object* v_getLevel_3650_; lean_object* v_congrInfo_3651_; lean_object* v_defEqI_3652_; lean_object* v_extensions_3653_; lean_object* v_issues_3654_; lean_object* v_instanceOverrides_3655_; uint8_t v_debug_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3677_; 
v___x_3643_ = lean_st_ref_take(v_a_3141_);
v_canon_3644_ = lean_ctor_get(v___x_3643_, 10);
v_share_3645_ = lean_ctor_get(v___x_3643_, 0);
v_maxFVar_3646_ = lean_ctor_get(v___x_3643_, 1);
v_proofInstInfo_3647_ = lean_ctor_get(v___x_3643_, 2);
v_proofInstInfoFVar_3648_ = lean_ctor_get(v___x_3643_, 3);
v_inferType_3649_ = lean_ctor_get(v___x_3643_, 4);
v_getLevel_3650_ = lean_ctor_get(v___x_3643_, 5);
v_congrInfo_3651_ = lean_ctor_get(v___x_3643_, 6);
v_defEqI_3652_ = lean_ctor_get(v___x_3643_, 7);
v_extensions_3653_ = lean_ctor_get(v___x_3643_, 8);
v_issues_3654_ = lean_ctor_get(v___x_3643_, 9);
v_instanceOverrides_3655_ = lean_ctor_get(v___x_3643_, 11);
v_debug_3656_ = lean_ctor_get_uint8(v___x_3643_, sizeof(void*)*12);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3658_ = v___x_3643_;
v_isShared_3659_ = v_isSharedCheck_3677_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_instanceOverrides_3655_);
lean_inc(v_canon_3644_);
lean_inc(v_issues_3654_);
lean_inc(v_extensions_3653_);
lean_inc(v_defEqI_3652_);
lean_inc(v_congrInfo_3651_);
lean_inc(v_getLevel_3650_);
lean_inc(v_inferType_3649_);
lean_inc(v_proofInstInfoFVar_3648_);
lean_inc(v_proofInstInfo_3647_);
lean_inc(v_maxFVar_3646_);
lean_inc(v_share_3645_);
lean_dec(v___x_3643_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3677_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v_cache_3660_; lean_object* v_cacheInType_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3676_; 
v_cache_3660_ = lean_ctor_get(v_canon_3644_, 0);
v_cacheInType_3661_ = lean_ctor_get(v_canon_3644_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_canon_3644_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3663_ = v_canon_3644_;
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_cacheInType_3661_);
lean_inc(v_cache_3660_);
lean_dec(v_canon_3644_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_inc(v_a_3639_);
v___x_3665_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3661_, v_e_3138_, v_a_3639_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3665_);
v___x_3667_ = v___x_3663_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_cache_3660_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 10, v___x_3667_);
v___x_3669_ = v___x_3658_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_share_3645_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_maxFVar_3646_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_proofInstInfo_3647_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_proofInstInfoFVar_3648_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_inferType_3649_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_getLevel_3650_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_congrInfo_3651_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_defEqI_3652_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_extensions_3653_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_issues_3654_);
lean_ctor_set(v_reuseFailAlloc_3674_, 10, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 11, v_instanceOverrides_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12, v_debug_3656_);
v___x_3669_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_st_ref_put(v_a_3141_, v___x_3669_);
if (v_isShared_3642_ == 0)
{
v___x_3672_ = v___x_3641_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3639_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 3);
return v___x_3638_;
}
}
}
}
case 10:
{
lean_object* v_data_3679_; lean_object* v_expr_3680_; lean_object* v___x_3681_; 
v_data_3679_ = lean_ctor_get(v_e_3138_, 0);
v_expr_3680_ = lean_ctor_get(v_e_3138_, 1);
lean_inc_ref(v_expr_3680_);
v___x_3681_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3680_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3696_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3696_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3696_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
size_t v___x_3686_; size_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_ptr_addr(v_expr_3680_);
v___x_3687_ = lean_ptr_addr(v_a_3682_);
v___x_3688_ = lean_usize_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_inc(v_data_3679_);
lean_dec_ref_known(v_e_3138_, 2);
v___x_3689_ = l_Lean_Expr_mdata___override(v_data_3679_, v_a_3682_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3689_);
v___x_3691_ = v___x_3684_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
else
{
lean_object* v___x_3694_; 
lean_dec(v_a_3682_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_e_3138_);
v___x_3694_ = v___x_3684_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_e_3138_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3138_, 2);
return v___x_3681_;
}
}
default: 
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_e_3138_);
return v___x_3697_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3138_ = stack[0].m_obj;
uint8_t v_a_3139_ = stack[1].m_num;
lean_object* v_a_3140_ = stack[2].m_obj;
lean_object* v_a_3141_ = stack[3].m_obj;
lean_object* v_a_3142_ = stack[4].m_obj;
lean_object* v_a_3143_ = stack[5].m_obj;
lean_object* v_a_3144_ = stack[6].m_obj;
lean_object* v_a_3145_ = stack[7].m_obj;
lean_object* v_res_3698_;
v_res_3698_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
stack->m_obj
 = v_res_3698_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3699_, uint8_t v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
if (v_a_3700_ == 0)
{
uint8_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = 1;
lean_inc_ref(v_e_3699_);
v___x_3709_ = l_Lean_Meta_isProp(v_e_3699_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; uint8_t v___x_3711_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v___x_3711_ = lean_unbox(v_a_3710_);
lean_dec(v_a_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3699_, v___x_3708_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3712_;
}
else
{
lean_object* v___x_3713_; 
v___x_3713_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3713_;
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v_e_3699_);
v_a_3714_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3709_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3709_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3722_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3699_ = stack[0].m_obj;
uint8_t v_a_3700_ = stack[1].m_num;
lean_object* v_a_3701_ = stack[2].m_obj;
lean_object* v_a_3702_ = stack[3].m_obj;
lean_object* v_a_3703_ = stack[4].m_obj;
lean_object* v_a_3704_ = stack[5].m_obj;
lean_object* v_a_3705_ = stack[6].m_obj;
lean_object* v_a_3706_ = stack[7].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
stack->m_obj
 = v_res_3723_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3724_, lean_object* v_e_3725_, uint8_t v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_){
_start:
{
if (lean_obj_tag(v_e_3725_) == 7)
{
lean_object* v_binderName_3734_; lean_object* v_binderType_3735_; lean_object* v_body_3736_; uint8_t v_binderInfo_3737_; lean_object* v___f_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_binderName_3734_ = lean_ctor_get(v_e_3725_, 0);
lean_inc(v_binderName_3734_);
v_binderType_3735_ = lean_ctor_get(v_e_3725_, 1);
lean_inc_ref(v_binderType_3735_);
v_body_3736_ = lean_ctor_get(v_e_3725_, 2);
lean_inc_ref(v_body_3736_);
v_binderInfo_3737_ = lean_ctor_get_uint8(v_e_3725_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3725_, 3);
lean_inc_ref(v_fvars_3724_);
v___f_3738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3738_, 0, v_fvars_3724_);
lean_closure_set(v___f_3738_, 1, v_body_3736_);
v___x_3739_ = lean_expr_instantiate_rev(v_binderType_3735_, v_fvars_3724_);
lean_dec_ref(v_fvars_3724_);
lean_dec_ref(v_binderType_3735_);
v___x_3740_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3739_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; uint8_t v___x_3742_; lean_object* v___x_3743_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = 0;
v___x_3743_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_3734_, v_binderInfo_3737_, v_a_3741_, v___f_3738_, v___x_3742_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
return v___x_3743_;
}
else
{
lean_dec_ref(v___f_3738_);
lean_dec(v_binderName_3734_);
return v___x_3740_;
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_expr_instantiate_rev(v_e_3725_, v_fvars_3724_);
lean_dec_ref(v_e_3725_);
v___x_3745_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3744_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; uint8_t v___x_3747_; uint8_t v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = 0;
v___x_3748_ = 1;
v___x_3749_ = 1;
v___x_3750_ = l_Lean_Meta_mkForallFVars(v_fvars_3724_, v_a_3746_, v___x_3747_, v___x_3748_, v___x_3748_, v___x_3749_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
lean_dec_ref(v_fvars_3724_);
return v___x_3750_;
}
else
{
lean_dec_ref(v_fvars_3724_);
return v___x_3745_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3724_ = stack[0].m_obj;
lean_object* v_e_3725_ = stack[1].m_obj;
uint8_t v_a_3726_ = stack[2].m_num;
lean_object* v_a_3727_ = stack[3].m_obj;
lean_object* v_a_3728_ = stack[4].m_obj;
lean_object* v_a_3729_ = stack[5].m_obj;
lean_object* v_a_3730_ = stack[6].m_obj;
lean_object* v_a_3731_ = stack[7].m_obj;
lean_object* v_a_3732_ = stack[8].m_obj;
lean_object* v_res_3751_;
v_res_3751_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3724_, v_e_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
stack->m_obj
 = v_res_3751_;
}
lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3752_, lean_object* v_body_3753_, lean_object* v_x_3754_, uint8_t v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_array_push(v_fvars_3752_, v_x_3754_);
v___x_3764_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3763_, v_body_3753_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
return v___x_3764_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3752_ = stack[0].m_obj;
lean_object* v_body_3753_ = stack[1].m_obj;
lean_object* v_x_3754_ = stack[2].m_obj;
uint8_t v___y_3755_ = stack[3].m_num;
lean_object* v___y_3756_ = stack[4].m_obj;
lean_object* v___y_3757_ = stack[5].m_obj;
lean_object* v___y_3758_ = stack[6].m_obj;
lean_object* v___y_3759_ = stack[7].m_obj;
lean_object* v___y_3760_ = stack[8].m_obj;
lean_object* v___y_3761_ = stack[9].m_obj;
lean_object* v_res_3765_;
v_res_3765_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3752_, v_body_3753_, v_x_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
stack->m_obj
 = v_res_3765_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
uint8_t v_a_boxed_3775_; lean_object* v_res_3776_; 
v_a_boxed_3775_ = lean_unbox(v_a_3767_);
v_res_3776_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3766_, v_a_boxed_3775_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
uint8_t v_a_boxed_3786_; lean_object* v_res_3787_; 
v_a_boxed_3786_ = lean_unbox(v_a_3778_);
v_res_3787_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3777_, v_a_boxed_3786_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
uint8_t v_a_boxed_3797_; lean_object* v_res_3798_; 
v_a_boxed_3797_ = lean_unbox(v_a_3789_);
v_res_3798_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3788_, v_a_boxed_3797_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
uint8_t v_a_boxed_3808_; lean_object* v_res_3809_; 
v_a_boxed_3808_ = lean_unbox(v_a_3800_);
v_res_3809_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3799_, v_a_boxed_3808_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
uint8_t v_a_boxed_3819_; lean_object* v_res_3820_; 
v_a_boxed_3819_ = lean_unbox(v_a_3811_);
v_res_3820_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3810_, v_a_boxed_3819_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3821_, lean_object* v_e_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_){
_start:
{
uint8_t v_a_boxed_3831_; lean_object* v_res_3832_; 
v_a_boxed_3831_ = lean_unbox(v_a_3823_);
v_res_3832_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3821_, v_e_3822_, v_a_boxed_3831_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3833_, lean_object* v_e_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
uint8_t v_a_boxed_3843_; lean_object* v_res_3844_; 
v_a_boxed_3843_ = lean_unbox(v_a_3835_);
v_res_3844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3833_, v_e_3834_, v_a_boxed_3843_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3845_, lean_object* v_report_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
uint8_t v_report_boxed_3855_; uint8_t v_a_boxed_3856_; lean_object* v_res_3857_; 
v_report_boxed_3855_ = lean_unbox(v_report_3846_);
v_a_boxed_3856_ = lean_unbox(v_a_3847_);
v_res_3857_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3845_, v_report_boxed_3855_, v_a_boxed_3856_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
uint8_t v_a_boxed_3867_; lean_object* v_res_3868_; 
v_a_boxed_3867_ = lean_unbox(v_a_3859_);
v_res_3868_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3858_, v_a_boxed_3867_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3869_, lean_object* v_e_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_){
_start:
{
uint8_t v_a_boxed_3879_; lean_object* v_res_3880_; 
v_a_boxed_3879_ = lean_unbox(v_a_3871_);
v_res_3880_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3869_, v_e_3870_, v_a_boxed_3879_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3881_, lean_object* v_00_u03b1_3882_, lean_object* v_c_3883_, lean_object* v_a_3884_, lean_object* v_b_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
uint8_t v_a_boxed_3894_; lean_object* v_res_3895_; 
v_a_boxed_3894_ = lean_unbox(v_a_3886_);
v_res_3895_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3881_, v_00_u03b1_3882_, v_c_3883_, v_a_3884_, v_b_3885_, v_a_boxed_3894_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3896_, lean_object* v_00_u03b1_3897_, lean_object* v_c_3898_, lean_object* v_inst_3899_, lean_object* v_a_3900_, lean_object* v_b_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
uint8_t v_a_boxed_3910_; lean_object* v_res_3911_; 
v_a_boxed_3910_ = lean_unbox(v_a_3902_);
v_res_3911_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3896_, v_00_u03b1_3897_, v_c_3898_, v_inst_3899_, v_a_3900_, v_b_3901_, v_a_boxed_3910_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
uint8_t v_a_boxed_3921_; lean_object* v_res_3922_; 
v_a_boxed_3921_ = lean_unbox(v_a_3913_);
v_res_3922_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3912_, v_a_boxed_3921_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
uint8_t v_a_boxed_3932_; lean_object* v_res_3933_; 
v_a_boxed_3932_ = lean_unbox(v_a_3924_);
v_res_3933_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3923_, v_a_boxed_3932_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3934_, lean_object* v_prop_3935_, lean_object* v_inst_3936_, lean_object* v_e_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
uint8_t v_a_boxed_3946_; lean_object* v_res_3947_; 
v_a_boxed_3946_ = lean_unbox(v_a_3938_);
v_res_3947_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3934_, v_prop_3935_, v_inst_3936_, v_e_3937_, v_a_boxed_3946_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3948_, lean_object* v_report_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
uint8_t v_report_boxed_3958_; uint8_t v_a_boxed_3959_; lean_object* v_res_3960_; 
v_report_boxed_3958_ = lean_unbox(v_report_3949_);
v_a_boxed_3959_ = lean_unbox(v_a_3950_);
v_res_3960_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3948_, v_report_boxed_3958_, v_a_boxed_3959_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3961_, lean_object* v_prop_3962_, lean_object* v_h_3963_, lean_object* v_e_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
uint8_t v_a_boxed_3973_; lean_object* v_res_3974_; 
v_a_boxed_3973_ = lean_unbox(v_a_3965_);
v_res_3974_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3961_, v_prop_3962_, v_h_3963_, v_e_3964_, v_a_boxed_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
uint8_t v_a_boxed_3984_; lean_object* v_res_3985_; 
v_a_boxed_3984_ = lean_unbox(v_a_3976_);
v_res_3985_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3975_, v_a_boxed_3984_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3986_, lean_object* v___x_3987_, lean_object* v_a_3988_, lean_object* v_b_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v___y_62967__boxed_3998_; lean_object* v_res_3999_; 
v___y_62967__boxed_3998_ = lean_unbox(v___y_3990_);
v_res_3999_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3986_, v___x_3987_, v_a_3988_, v_b_3989_, v___y_62967__boxed_3998_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v___x_3987_);
lean_dec(v_upperBound_3986_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_4000_, lean_object* v_snd_4001_, lean_object* v_a_4002_, lean_object* v___x_4003_, lean_object* v_fst_4004_, lean_object* v___x_4005_, lean_object* v_____r_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
uint8_t v___x_63031__boxed_4015_; uint8_t v___y_63034__boxed_4016_; lean_object* v_res_4017_; 
v___x_63031__boxed_4015_ = lean_unbox(v___x_4003_);
v___y_63034__boxed_4016_ = lean_unbox(v___y_4007_);
v_res_4017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_4000_, v_snd_4001_, v_a_4002_, v___x_63031__boxed_4015_, v_fst_4004_, v___x_4005_, v_____r_4006_, v___y_63034__boxed_4016_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v___x_4005_);
lean_dec(v_a_4002_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
uint8_t v_a_boxed_4027_; lean_object* v_res_4028_; 
v_a_boxed_4027_ = lean_unbox(v_a_4019_);
v_res_4028_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_4018_, v_a_boxed_4027_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_4029_, lean_object* v_prop_4030_, lean_object* v_h_4031_, lean_object* v_e_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
uint8_t v_a_boxed_4041_; lean_object* v_res_4042_; 
v_a_boxed_4041_ = lean_unbox(v_a_4033_);
v_res_4042_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_4029_, v_prop_4030_, v_h_4031_, v_e_4032_, v_a_boxed_4041_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_, lean_object* v_x_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
uint8_t v___y_63211__boxed_4055_; lean_object* v_res_4056_; 
v___y_63211__boxed_4055_ = lean_unbox(v___y_4047_);
v_res_4056_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_4043_, v_x_4044_, v_x_4045_, v_x_4046_, v___y_63211__boxed_4055_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
uint8_t v_a_boxed_4066_; lean_object* v_res_4067_; 
v_a_boxed_4066_ = lean_unbox(v_a_4058_);
v_res_4067_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4057_, v_a_boxed_4066_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
return v_res_4067_;
}
}
lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_4068_, uint8_t v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_4068_, v___y_4075_);
return v___x_4077_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4068_ = stack[0].m_obj;
uint8_t v___y_4069_ = stack[1].m_num;
lean_object* v___y_4070_ = stack[2].m_obj;
lean_object* v___y_4071_ = stack[3].m_obj;
lean_object* v___y_4072_ = stack[4].m_obj;
lean_object* v___y_4073_ = stack[5].m_obj;
lean_object* v___y_4074_ = stack[6].m_obj;
lean_object* v___y_4075_ = stack[7].m_obj;
lean_object* v_res_4078_;
v_res_4078_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
stack->m_obj
 = v_res_4078_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
uint8_t v___y_67350__boxed_4088_; lean_object* v_res_4089_; 
v___y_67350__boxed_4088_ = lean_unbox(v___y_4080_);
v_res_4089_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4079_, v___y_67350__boxed_4088_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
return v_res_4089_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_4090_, uint8_t v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_4090_, v___y_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4090_ = stack[0].m_obj;
uint8_t v___y_4091_ = stack[1].m_num;
lean_object* v___y_4092_ = stack[2].m_obj;
lean_object* v___y_4093_ = stack[3].m_obj;
lean_object* v___y_4094_ = stack[4].m_obj;
lean_object* v___y_4095_ = stack[5].m_obj;
lean_object* v___y_4096_ = stack[6].m_obj;
lean_object* v___y_4097_ = stack[7].m_obj;
lean_object* v_res_4100_;
v_res_4100_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
uint8_t v___y_67393__boxed_4110_; lean_object* v_res_4111_; 
v___y_67393__boxed_4110_ = lean_unbox(v___y_4102_);
v_res_4111_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4101_, v___y_67393__boxed_4110_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4111_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object* v_00_u03b1_4112_, lean_object* v_name_4113_, lean_object* v_type_4114_, lean_object* v_val_4115_, lean_object* v_k_4116_, uint8_t v_nondep_4117_, uint8_t v_kind_4118_, uint8_t v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_4113_, v_type_4114_, v_val_4115_, v_k_4116_, v_nondep_4117_, v_kind_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4113_ = stack[1].m_obj;
lean_object* v_type_4114_ = stack[2].m_obj;
lean_object* v_val_4115_ = stack[3].m_obj;
lean_object* v_k_4116_ = stack[4].m_obj;
uint8_t v_nondep_4117_ = stack[5].m_num;
uint8_t v_kind_4118_ = stack[6].m_num;
uint8_t v___y_4119_ = stack[7].m_num;
lean_object* v___y_4120_ = stack[8].m_obj;
lean_object* v___y_4121_ = stack[9].m_obj;
lean_object* v___y_4122_ = stack[10].m_obj;
lean_object* v___y_4123_ = stack[11].m_obj;
lean_object* v___y_4124_ = stack[12].m_obj;
lean_object* v___y_4125_ = stack[13].m_obj;
lean_object* v_res_4128_;
v_res_4128_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_box(0), v_name_4113_, v_type_4114_, v_val_4115_, v_k_4116_, v_nondep_4117_, v_kind_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
stack->m_obj
 = v_res_4128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object* v_00_u03b1_4129_, lean_object* v_name_4130_, lean_object* v_type_4131_, lean_object* v_val_4132_, lean_object* v_k_4133_, lean_object* v_nondep_4134_, lean_object* v_kind_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
uint8_t v_nondep_boxed_4144_; uint8_t v_kind_boxed_4145_; uint8_t v___y_67436__boxed_4146_; lean_object* v_res_4147_; 
v_nondep_boxed_4144_ = lean_unbox(v_nondep_4134_);
v_kind_boxed_4145_ = lean_unbox(v_kind_4135_);
v___y_67436__boxed_4146_ = lean_unbox(v___y_4136_);
v_res_4147_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(v_00_u03b1_4129_, v_name_4130_, v_type_4131_, v_val_4132_, v_k_4133_, v_nondep_boxed_4144_, v_kind_boxed_4145_, v___y_67436__boxed_4146_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
return v_res_4147_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object* v_00_u03b1_4148_, lean_object* v_name_4149_, uint8_t v_bi_4150_, lean_object* v_type_4151_, lean_object* v_k_4152_, uint8_t v_kind_4153_, uint8_t v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_4149_, v_bi_4150_, v_type_4151_, v_k_4152_, v_kind_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
return v___x_4162_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4149_ = stack[1].m_obj;
uint8_t v_bi_4150_ = stack[2].m_num;
lean_object* v_type_4151_ = stack[3].m_obj;
lean_object* v_k_4152_ = stack[4].m_obj;
uint8_t v_kind_4153_ = stack[5].m_num;
uint8_t v___y_4154_ = stack[6].m_num;
lean_object* v___y_4155_ = stack[7].m_obj;
lean_object* v___y_4156_ = stack[8].m_obj;
lean_object* v___y_4157_ = stack[9].m_obj;
lean_object* v___y_4158_ = stack[10].m_obj;
lean_object* v___y_4159_ = stack[11].m_obj;
lean_object* v___y_4160_ = stack[12].m_obj;
lean_object* v_res_4163_;
v_res_4163_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_box(0), v_name_4149_, v_bi_4150_, v_type_4151_, v_k_4152_, v_kind_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
stack->m_obj
 = v_res_4163_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object* v_00_u03b1_4164_, lean_object* v_name_4165_, lean_object* v_bi_4166_, lean_object* v_type_4167_, lean_object* v_k_4168_, lean_object* v_kind_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v_bi_boxed_4178_; uint8_t v_kind_boxed_4179_; uint8_t v___y_67479__boxed_4180_; lean_object* v_res_4181_; 
v_bi_boxed_4178_ = lean_unbox(v_bi_4166_);
v_kind_boxed_4179_ = lean_unbox(v_kind_4169_);
v___y_67479__boxed_4180_ = lean_unbox(v___y_4170_);
v_res_4181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(v_00_u03b1_4164_, v_name_4165_, v_bi_boxed_4178_, v_type_4167_, v_k_4168_, v_kind_boxed_4179_, v___y_67479__boxed_4180_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4182_, lean_object* v_m_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4183_, v_a_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4186_, lean_object* v_m_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4186_, v_m_4187_, v_a_4188_);
lean_dec_ref(v_a_4188_);
lean_dec_ref(v_m_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4190_, lean_object* v_m_4191_, lean_object* v_a_4192_, lean_object* v_b_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4191_, v_a_4192_, v_b_4193_);
return v___x_4194_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4195_, lean_object* v_msg_4196_, uint8_t v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4195_, v_msg_4196_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4195_ = stack[0].m_obj;
lean_object* v_msg_4196_ = stack[1].m_obj;
uint8_t v___y_4197_ = stack[2].m_num;
lean_object* v___y_4198_ = stack[3].m_obj;
lean_object* v___y_4199_ = stack[4].m_obj;
lean_object* v___y_4200_ = stack[5].m_obj;
lean_object* v___y_4201_ = stack[6].m_obj;
lean_object* v___y_4202_ = stack[7].m_obj;
lean_object* v___y_4203_ = stack[8].m_obj;
lean_object* v_res_4206_;
v_res_4206_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4195_, v_msg_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
stack->m_obj
 = v_res_4206_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4207_, lean_object* v_msg_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v___y_67528__boxed_4217_; lean_object* v_res_4218_; 
v___y_67528__boxed_4217_ = lean_unbox(v___y_4209_);
v_res_4218_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4207_, v_msg_4208_, v___y_67528__boxed_4217_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4218_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4219_, lean_object* v___x_4220_, lean_object* v___x_4221_, lean_object* v_inst_4222_, lean_object* v_R_4223_, lean_object* v_a_4224_, lean_object* v_b_4225_, lean_object* v_c_4226_, uint8_t v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4219_, v___x_4221_, v_a_4224_, v_b_4225_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4219_ = stack[0].m_obj;
lean_object* v___x_4220_ = stack[1].m_obj;
lean_object* v___x_4221_ = stack[2].m_obj;
lean_object* v_a_4224_ = stack[5].m_obj;
lean_object* v_b_4225_ = stack[6].m_obj;
uint8_t v___y_4227_ = stack[8].m_num;
lean_object* v___y_4228_ = stack[9].m_obj;
lean_object* v___y_4229_ = stack[10].m_obj;
lean_object* v___y_4230_ = stack[11].m_obj;
lean_object* v___y_4231_ = stack[12].m_obj;
lean_object* v___y_4232_ = stack[13].m_obj;
lean_object* v___y_4233_ = stack[14].m_obj;
lean_object* v_res_4236_;
v_res_4236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4219_, v___x_4220_, v___x_4221_, lean_box(0), lean_box(0), v_a_4224_, v_b_4225_, lean_box(0), v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
stack->m_obj
 = v_res_4236_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4237_, lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v_inst_4240_, lean_object* v_R_4241_, lean_object* v_a_4242_, lean_object* v_b_4243_, lean_object* v_c_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v___y_67575__boxed_4253_; lean_object* v_res_4254_; 
v___y_67575__boxed_4253_ = lean_unbox(v___y_4245_);
v_res_4254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4237_, v___x_4238_, v___x_4239_, v_inst_4240_, v_R_4241_, v_a_4242_, v_b_4243_, v_c_4244_, v___y_67575__boxed_4253_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec_ref(v___x_4239_);
lean_dec(v___x_4238_);
lean_dec(v_upperBound_4237_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4255_, lean_object* v_a_4256_, lean_object* v_x_4257_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4256_, v_x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4259_, lean_object* v_a_4260_, lean_object* v_x_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4259_, v_a_4260_, v_x_4261_);
lean_dec(v_x_4261_);
lean_dec_ref(v_a_4260_);
return v_res_4262_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4263_, lean_object* v_a_4264_, lean_object* v_x_4265_){
_start:
{
uint8_t v___x_4266_; 
v___x_4266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4264_, v_x_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4264_ = stack[1].m_obj;
lean_object* v_x_4265_ = stack[2].m_obj;
uint8_t v_res_4267_;
v_res_4267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_box(0), v_a_4264_, v_x_4265_);
stack->m_num = v_res_4267_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4268_, lean_object* v_a_4269_, lean_object* v_x_4270_){
_start:
{
uint8_t v_res_4271_; lean_object* v_r_4272_; 
v_res_4271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4268_, v_a_4269_, v_x_4270_);
lean_dec(v_x_4270_);
lean_dec_ref(v_a_4269_);
v_r_4272_ = lean_box(v_res_4271_);
return v_r_4272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4273_, lean_object* v_data_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4276_, lean_object* v_a_4277_, lean_object* v_b_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4277_, v_b_4278_, v_x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object* v_00_u03b2_4281_, lean_object* v_i_4282_, lean_object* v_source_4283_, lean_object* v_target_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v_i_4282_, v_source_4283_, v_target_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object* v_00_u03b2_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_x_4287_, v_x_4288_);
return v___x_4289_;
}
}
lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4290_, lean_object* v_i_4291_, lean_object* v_arg_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4290_, v_i_4291_, v_arg_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4314_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4314_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4314_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
uint8_t v___x_4303_; 
v___x_4303_ = lean_unbox(v_a_4299_);
lean_dec(v_a_4299_);
if (v___x_4303_ == 3)
{
uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4304_ = 0;
v___x_4305_ = lean_box(v___x_4304_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4305_);
v___x_4307_ = v___x_4301_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
else
{
uint8_t v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4309_ = 1;
v___x_4310_ = lean_box(v___x_4309_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4310_);
v___x_4312_ = v___x_4301_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
v_a_4315_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4298_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4298_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Canon_isSupport_0interp(lean_interpreter_value* stack)
{
lean_object* v_pinfos_4290_ = stack[0].m_obj;
lean_object* v_i_4291_ = stack[1].m_obj;
lean_object* v_arg_4292_ = stack[2].m_obj;
lean_object* v_a_4293_ = stack[3].m_obj;
lean_object* v_a_4294_ = stack[4].m_obj;
lean_object* v_a_4295_ = stack[5].m_obj;
lean_object* v_a_4296_ = stack[6].m_obj;
lean_object* v_res_4323_;
v_res_4323_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4290_, v_i_4291_, v_arg_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
stack->m_obj
 = v_res_4323_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4324_, lean_object* v_i_4325_, lean_object* v_arg_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4324_, v_i_4325_, v_arg_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_i_4325_);
lean_dec_ref(v_pinfos_4324_);
return v_res_4332_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4333_, lean_object* v_opts_4334_, lean_object* v_act_4335_, lean_object* v_decl_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_inc(v___y_4342_);
lean_inc_ref(v___y_4341_);
lean_inc(v___y_4340_);
lean_inc_ref(v___y_4339_);
lean_inc(v___y_4338_);
lean_inc_ref(v___y_4337_);
v___x_4344_ = lean_apply_6(v_act_4335_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
v___x_4345_ = l_Lean_profileitIOUnsafe___redArg(v_category_4333_, v_opts_4334_, v___x_4344_, v_decl_4336_);
return v___x_4345_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_4333_ = stack[0].m_obj;
lean_object* v_opts_4334_ = stack[1].m_obj;
lean_object* v_act_4335_ = stack[2].m_obj;
lean_object* v_decl_4336_ = stack[3].m_obj;
lean_object* v___y_4337_ = stack[4].m_obj;
lean_object* v___y_4338_ = stack[5].m_obj;
lean_object* v___y_4339_ = stack[6].m_obj;
lean_object* v___y_4340_ = stack[7].m_obj;
lean_object* v___y_4341_ = stack[8].m_obj;
lean_object* v___y_4342_ = stack[9].m_obj;
lean_object* v_res_4346_;
v_res_4346_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4333_, v_opts_4334_, v_act_4335_, v_decl_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
stack->m_obj
 = v_res_4346_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4347_, lean_object* v_opts_4348_, lean_object* v_act_4349_, lean_object* v_decl_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4347_, v_opts_4348_, v_act_4349_, v_decl_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec_ref(v_opts_4348_);
lean_dec_ref(v_category_4347_);
return v_res_4358_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4359_, lean_object* v_category_4360_, lean_object* v_opts_4361_, lean_object* v_act_4362_, lean_object* v_decl_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4360_, v_opts_4361_, v_act_4362_, v_decl_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_4360_ = stack[1].m_obj;
lean_object* v_opts_4361_ = stack[2].m_obj;
lean_object* v_act_4362_ = stack[3].m_obj;
lean_object* v_decl_4363_ = stack[4].m_obj;
lean_object* v___y_4364_ = stack[5].m_obj;
lean_object* v___y_4365_ = stack[6].m_obj;
lean_object* v___y_4366_ = stack[7].m_obj;
lean_object* v___y_4367_ = stack[8].m_obj;
lean_object* v___y_4368_ = stack[9].m_obj;
lean_object* v___y_4369_ = stack[10].m_obj;
lean_object* v_res_4372_;
v_res_4372_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_box(0), v_category_4360_, v_opts_4361_, v_act_4362_, v_decl_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
stack->m_obj
 = v_res_4372_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4373_, lean_object* v_category_4374_, lean_object* v_opts_4375_, lean_object* v_act_4376_, lean_object* v_decl_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4373_, v_category_4374_, v_opts_4375_, v_act_4376_, v_decl_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec_ref(v_opts_4375_);
lean_dec_ref(v_category_4374_);
return v_res_4385_;
}
}
lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4386_, lean_object* v_e_4387_, uint8_t v___x_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___y_4397_; lean_object* v___x_4406_; uint8_t v_transparency_4407_; uint8_t v___x_4408_; 
v___x_4406_ = l_Lean_Meta_Context_config(v___y_4391_);
v_transparency_4407_ = lean_ctor_get_uint8(v___x_4406_, 9);
lean_dec_ref(v___x_4406_);
v___x_4408_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4407_, v___x_4386_);
if (v___x_4408_ == 0)
{
lean_object* v_keyedConfig_4409_; uint8_t v_trackZetaDelta_4410_; lean_object* v_zetaDeltaSet_4411_; lean_object* v_lctx_4412_; lean_object* v_localInstances_4413_; lean_object* v_defEqCtx_x3f_4414_; lean_object* v_synthPendingDepth_4415_; lean_object* v_customCanUnfoldPredicate_x3f_4416_; uint8_t v_univApprox_4417_; uint8_t v_inTypeClassResolution_4418_; uint8_t v_cacheInferType_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_keyedConfig_4409_ = lean_ctor_get(v___y_4391_, 0);
v_trackZetaDelta_4410_ = lean_ctor_get_uint8(v___y_4391_, sizeof(void*)*7);
v_zetaDeltaSet_4411_ = lean_ctor_get(v___y_4391_, 1);
v_lctx_4412_ = lean_ctor_get(v___y_4391_, 2);
v_localInstances_4413_ = lean_ctor_get(v___y_4391_, 3);
v_defEqCtx_x3f_4414_ = lean_ctor_get(v___y_4391_, 4);
v_synthPendingDepth_4415_ = lean_ctor_get(v___y_4391_, 5);
v_customCanUnfoldPredicate_x3f_4416_ = lean_ctor_get(v___y_4391_, 6);
v_univApprox_4417_ = lean_ctor_get_uint8(v___y_4391_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4418_ = lean_ctor_get_uint8(v___y_4391_, sizeof(void*)*7 + 2);
v_cacheInferType_4419_ = lean_ctor_get_uint8(v___y_4391_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4409_);
v___x_4420_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4386_, v_keyedConfig_4409_);
lean_inc(v_customCanUnfoldPredicate_x3f_4416_);
lean_inc(v_synthPendingDepth_4415_);
lean_inc(v_defEqCtx_x3f_4414_);
lean_inc_ref(v_localInstances_4413_);
lean_inc_ref(v_lctx_4412_);
lean_inc(v_zetaDeltaSet_4411_);
v___x_4421_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
lean_ctor_set(v___x_4421_, 1, v_zetaDeltaSet_4411_);
lean_ctor_set(v___x_4421_, 2, v_lctx_4412_);
lean_ctor_set(v___x_4421_, 3, v_localInstances_4413_);
lean_ctor_set(v___x_4421_, 4, v_defEqCtx_x3f_4414_);
lean_ctor_set(v___x_4421_, 5, v_synthPendingDepth_4415_);
lean_ctor_set(v___x_4421_, 6, v_customCanUnfoldPredicate_x3f_4416_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*7, v_trackZetaDelta_4410_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*7 + 1, v_univApprox_4417_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4418_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*7 + 3, v_cacheInferType_4419_);
v___x_4422_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4387_, v___x_4388_, v___y_4389_, v___y_4390_, v___x_4421_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec_ref_known(v___x_4421_, 7);
v___y_4397_ = v___x_4422_;
goto v___jp_4396_;
}
else
{
lean_object* v___x_4423_; 
v___x_4423_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4387_, v___x_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
v___y_4397_ = v___x_4423_;
goto v___jp_4396_;
}
v___jp_4396_:
{
if (lean_obj_tag(v___y_4397_) == 0)
{
return v___y_4397_;
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
v_a_4398_ = lean_ctor_get(v___y_4397_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___y_4397_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___y_4397_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___y_4397_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_canon___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4386_ = stack[0].m_num;
lean_object* v_e_4387_ = stack[1].m_obj;
uint8_t v___x_4388_ = stack[2].m_num;
lean_object* v___y_4389_ = stack[3].m_obj;
lean_object* v___y_4390_ = stack[4].m_obj;
lean_object* v___y_4391_ = stack[5].m_obj;
lean_object* v___y_4392_ = stack[6].m_obj;
lean_object* v___y_4393_ = stack[7].m_obj;
lean_object* v___y_4394_ = stack[8].m_obj;
lean_object* v_res_4424_;
v_res_4424_ = l_Lean_Meta_Sym_canon___lam__0(v___x_4386_, v_e_4387_, v___x_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
stack->m_obj
 = v_res_4424_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4425_, lean_object* v_e_4426_, lean_object* v___x_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v___x_2148__boxed_4435_; uint8_t v___x_2149__boxed_4436_; lean_object* v_res_4437_; 
v___x_2148__boxed_4435_ = lean_unbox(v___x_4425_);
v___x_2149__boxed_4436_ = lean_unbox(v___x_4427_);
v_res_4437_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2148__boxed_4435_, v_e_4426_, v___x_2149__boxed_4436_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4437_;
}
}
lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4447_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4444_);
v___x_4448_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4449_ = 0;
v___x_4450_ = 2;
v___x_4451_ = lean_box(v___x_4450_);
v___x_4452_ = lean_box(v___x_4449_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4453_, 0, v___x_4451_);
lean_closure_set(v___f_4453_, 1, v_e_4439_);
lean_closure_set(v___f_4453_, 2, v___x_4452_);
v___x_4454_ = lean_box(0);
v___x_4455_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4448_, v___x_4447_, v___f_4453_, v___x_4454_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
lean_dec_ref(v___x_4447_);
return v___x_4455_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_canon_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4439_ = stack[0].m_obj;
lean_object* v_a_4440_ = stack[1].m_obj;
lean_object* v_a_4441_ = stack[2].m_obj;
lean_object* v_a_4442_ = stack[3].m_obj;
lean_object* v_a_4443_ = stack[4].m_obj;
lean_object* v_a_4444_ = stack[5].m_obj;
lean_object* v_a_4445_ = stack[6].m_obj;
lean_object* v_res_4456_;
v_res_4456_ = l_Lean_Meta_Sym_canon(v_e_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
stack->m_obj
 = v_res_4456_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_Meta_Sym_canon(v_e_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
return v_res_4465_;
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

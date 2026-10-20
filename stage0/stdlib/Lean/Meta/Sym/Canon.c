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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nfailed to synthesize"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v_modified_172_; 
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_113_, v___y_110_);
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
v___y_110_ = v___y_142_;
v___y_111_ = v_args_140_;
v___y_112_ = v_modified_141_;
v___y_113_ = v_inst_144_;
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
v___y_111_ = v_args_140_;
v___y_112_ = v_modified_141_;
v___y_113_ = v_inst_144_;
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
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_box(0);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7));
v___x_284_ = l_Lean_mkConst(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_287_ = l_Lean_mkConst(v___x_286_, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_297_; 
lean_inc_ref(v_e_288_);
v___x_297_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_288_, v_a_290_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_552_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_552_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_552_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_552_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = l_Lean_Expr_cleanupAnnotations(v_a_298_);
v___x_303_ = l_Lean_Expr_isApp(v___x_302_);
if (v___x_303_ == 0)
{
lean_dec_ref(v___x_302_);
lean_del_object(v___x_300_);
lean_dec_ref(v_e_288_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_arg_304_ = lean_ctor_get(v___x_302_, 1);
lean_inc_ref(v_arg_304_);
v___x_305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_302_);
v___x_306_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; 
lean_del_object(v___x_300_);
v___x_308_ = l_Lean_Expr_isApp(v___x_305_);
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_e_288_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_arg_309_ = lean_ctor_get(v___x_305_, 1);
lean_inc_ref(v_arg_309_);
v___x_310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_305_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_e_288_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_arg_314_ = lean_ctor_get(v___x_310_, 1);
lean_inc_ref(v_arg_314_);
v___x_315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_317_ = l_Lean_Expr_isConstOf(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; 
lean_dec_ref(v_arg_309_);
v___x_318_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_319_ = l_Lean_Expr_isConstOf(v___x_315_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_304_);
v___x_320_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_321_ = l_Lean_Expr_isConstOf(v___x_315_, v___x_320_);
lean_dec_ref(v___x_315_);
if (v___x_321_ == 0)
{
lean_dec_ref(v_e_288_);
goto v___jp_294_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_322_;
}
}
else
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v_e_288_);
v___x_323_ = l_Lean_Meta_getNatValue_x3f(v_arg_314_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_314_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_386_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_386_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_386_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_386_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
if (lean_obj_tag(v_a_324_) == 1)
{
lean_object* v_val_328_; lean_object* v___x_329_; 
lean_del_object(v___x_326_);
v_val_328_ = lean_ctor_get(v_a_324_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v_a_324_, 1);
v___x_329_ = l_Lean_Meta_getNatValue_x3f(v_arg_304_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_304_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_373_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_373_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
if (lean_obj_tag(v_a_330_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_368_; 
v_val_334_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_368_ == 0)
{
v___x_336_ = v_a_330_;
v_isShared_337_ = v_isSharedCheck_368_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v_a_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_368_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_dec_eq(v_val_328_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_332_);
v___x_340_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8);
lean_inc(v_val_328_);
v___x_341_ = l_Lean_mkNatLit(v_val_328_);
v___x_342_ = l_Lean_Expr_app___override(v___x_340_, v___x_341_);
v___x_343_ = lean_nat_mod(v_val_334_, v_val_328_);
lean_dec(v_val_328_);
lean_dec(v_val_334_);
v___x_344_ = l_Lean_Meta_mkNumeral(v___x_342_, v___x_343_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v_a_345_);
v___x_350_ = v___x_336_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_350_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_del_object(v___x_336_);
v_a_356_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_344_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_344_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_366_; 
lean_del_object(v___x_336_);
lean_dec(v_val_334_);
lean_dec(v_val_328_);
v___x_364_ = lean_box(0);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_364_);
v___x_366_ = v___x_332_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec(v_a_330_);
lean_dec(v_val_328_);
v___x_369_ = lean_box(0);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_369_);
v___x_371_ = v___x_332_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_val_328_);
v_a_374_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_329_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_329_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
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
else
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec(v_a_324_);
lean_dec_ref(v_arg_304_);
v___x_382_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_382_);
v___x_384_ = v___x_326_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_arg_304_);
v_a_387_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_323_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_323_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_e_288_);
lean_inc_ref(v_arg_314_);
v___x_395_ = l_Lean_Meta_getLitValueModulus_x3f(v_arg_314_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_457_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_457_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_457_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_457_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
if (lean_obj_tag(v_a_396_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_401_; 
v_val_400_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_a_396_, 1);
v___x_401_ = l_Lean_Meta_getNatValue_x3f(v_arg_309_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_309_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_444_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_444_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_444_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_444_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
if (lean_obj_tag(v_a_402_) == 1)
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_439_; 
lean_del_object(v___x_398_);
v_val_411_ = lean_ctor_get(v_a_402_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_402_);
if (v_isSharedCheck_439_ == 0)
{
v___x_413_ = v_a_402_;
v_isShared_414_ = v_isSharedCheck_439_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v_a_402_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_439_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_nat_dec_eq(v_val_400_, v___x_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_nat_dec_lt(v_val_411_, v_val_400_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_del_object(v___x_404_);
v___x_418_ = lean_nat_mod(v_val_411_, v_val_400_);
lean_dec(v_val_400_);
lean_dec(v_val_411_);
v___x_419_ = l_Lean_Meta_mkNumeral(v_arg_314_, v___x_418_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_a_420_);
v___x_425_ = v___x_413_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_425_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_413_);
v_a_431_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_419_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_419_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_del_object(v___x_413_);
lean_dec(v_val_411_);
lean_dec(v_val_400_);
lean_dec_ref(v_arg_314_);
goto v___jp_406_;
}
}
else
{
lean_del_object(v___x_413_);
lean_dec(v_val_411_);
lean_dec(v_val_400_);
lean_dec_ref(v_arg_314_);
goto v___jp_406_;
}
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_del_object(v___x_404_);
lean_dec(v_a_402_);
lean_dec(v_val_400_);
lean_dec_ref(v_arg_314_);
v___x_440_ = lean_box(0);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_440_);
v___x_442_ = v___x_398_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_val_400_);
lean_del_object(v___x_398_);
lean_dec_ref(v_arg_314_);
v_a_445_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_401_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_401_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec(v_a_396_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_309_);
v___x_453_ = lean_box(0);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_453_);
v___x_455_ = v___x_398_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_309_);
v_a_458_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_395_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_395_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v___x_310_);
v___x_466_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
if (lean_obj_tag(v_a_467_) == 1)
{
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_304_);
return v___x_466_;
}
else
{
lean_object* v___x_468_; 
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_Meta_getNatValue_x3f(v_arg_304_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_304_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_504_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_504_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_499_; 
lean_del_object(v___x_471_);
v_val_473_ = lean_ctor_get(v_a_469_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_499_ == 0)
{
v___x_475_ = v_a_469_;
v_isShared_476_ = v_isSharedCheck_499_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_val_473_);
lean_dec(v_a_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_499_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2);
v___x_478_ = l_Lean_Expr_app___override(v___x_477_, v_arg_309_);
v___x_479_ = l_Lean_Meta_mkNumeral(v___x_478_, v_val_473_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_a_480_);
v___x_485_ = v___x_475_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_475_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec(v_a_469_);
lean_dec_ref(v_arg_309_);
v___x_500_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_500_);
v___x_502_ = v___x_471_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
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
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_arg_309_);
v_a_505_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_468_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_468_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_304_);
return v___x_466_;
}
}
}
}
else
{
uint8_t v___x_513_; 
lean_dec_ref(v___x_305_);
v___x_513_ = l_Lean_Expr_isCharLit(v_e_288_);
lean_dec_ref(v_e_288_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_del_object(v___x_300_);
v___x_514_ = l_Lean_Meta_getNatValue_x3f(v_arg_304_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_304_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_539_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_539_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
if (lean_obj_tag(v_a_515_) == 1)
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_534_; 
v_val_519_ = lean_ctor_get(v_a_515_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_534_ == 0)
{
v___x_521_ = v_a_515_;
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v_a_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint32_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_523_ = l_Char_ofNat(v_val_519_);
lean_dec(v_val_519_);
v___x_524_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9);
v___x_525_ = lean_uint32_to_nat(v___x_523_);
v___x_526_ = l_Lean_mkRawNatLit(v___x_525_);
v___x_527_ = l_Lean_Expr_app___override(v___x_524_, v___x_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_529_);
v___x_531_ = v___x_517_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec(v_a_515_);
v___x_535_ = lean_box(0);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_535_);
v___x_537_ = v___x_517_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_514_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_514_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec_ref(v_arg_304_);
v___x_548_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_548_);
v___x_550_ = v___x_300_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_e_288_);
v_a_553_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_297_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_297_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_570_, lean_object* v_k_571_, uint8_t v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_572_ == 0)
{
lean_object* v___x_582_; lean_object* v_canon_583_; lean_object* v_cache_584_; lean_object* v___x_585_; 
v___x_582_ = lean_st_ref_get(v_a_574_);
v_canon_583_ = lean_ctor_get(v___x_582_, 10);
lean_inc_ref(v_canon_583_);
lean_dec(v___x_582_);
v_cache_584_ = lean_ctor_get(v_canon_583_, 0);
lean_inc_ref(v_cache_584_);
lean_dec_ref(v_canon_583_);
lean_inc_ref(v_e_570_);
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_580_, v___x_581_, v_cache_584_, v_e_570_);
lean_dec_ref(v_cache_584_);
if (lean_obj_tag(v___x_585_) == 1)
{
lean_object* v_val_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_k_571_);
lean_dec_ref(v_e_570_);
v_val_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_val_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 0);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_val_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_585_);
v___x_594_ = lean_box(v_a_572_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_595_ = lean_apply_8(v_k_571_, v___x_594_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_635_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_635_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v_canon_601_; lean_object* v_share_602_; lean_object* v_maxFVar_603_; lean_object* v_proofInstInfo_604_; lean_object* v_proofInstInfoFVar_605_; lean_object* v_inferType_606_; lean_object* v_getLevel_607_; lean_object* v_congrInfo_608_; lean_object* v_defEqI_609_; lean_object* v_extensions_610_; lean_object* v_issues_611_; lean_object* v_instanceOverrides_612_; uint8_t v_debug_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_634_; 
v___x_600_ = lean_st_ref_take(v_a_574_);
v_canon_601_ = lean_ctor_get(v___x_600_, 10);
v_share_602_ = lean_ctor_get(v___x_600_, 0);
v_maxFVar_603_ = lean_ctor_get(v___x_600_, 1);
v_proofInstInfo_604_ = lean_ctor_get(v___x_600_, 2);
v_proofInstInfoFVar_605_ = lean_ctor_get(v___x_600_, 3);
v_inferType_606_ = lean_ctor_get(v___x_600_, 4);
v_getLevel_607_ = lean_ctor_get(v___x_600_, 5);
v_congrInfo_608_ = lean_ctor_get(v___x_600_, 6);
v_defEqI_609_ = lean_ctor_get(v___x_600_, 7);
v_extensions_610_ = lean_ctor_get(v___x_600_, 8);
v_issues_611_ = lean_ctor_get(v___x_600_, 9);
v_instanceOverrides_612_ = lean_ctor_get(v___x_600_, 11);
v_debug_613_ = lean_ctor_get_uint8(v___x_600_, sizeof(void*)*12);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_634_ == 0)
{
v___x_615_ = v___x_600_;
v_isShared_616_ = v_isSharedCheck_634_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_instanceOverrides_612_);
lean_inc(v_canon_601_);
lean_inc(v_issues_611_);
lean_inc(v_extensions_610_);
lean_inc(v_defEqI_609_);
lean_inc(v_congrInfo_608_);
lean_inc(v_getLevel_607_);
lean_inc(v_inferType_606_);
lean_inc(v_proofInstInfoFVar_605_);
lean_inc(v_proofInstInfo_604_);
lean_inc(v_maxFVar_603_);
lean_inc(v_share_602_);
lean_dec(v___x_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_634_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_cache_617_; lean_object* v_cacheInType_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_633_; 
v_cache_617_ = lean_ctor_get(v_canon_601_, 0);
v_cacheInType_618_ = lean_ctor_get(v_canon_601_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_canon_601_);
if (v_isSharedCheck_633_ == 0)
{
v___x_620_ = v_canon_601_;
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_cacheInType_618_);
lean_inc(v_cache_617_);
lean_dec(v_canon_601_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
lean_inc(v_a_596_);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_580_, v___x_581_, v_cache_617_, v_e_570_, v_a_596_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_cacheInType_618_);
v___x_624_ = v_reuseFailAlloc_632_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 10, v___x_624_);
v___x_626_ = v___x_615_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_share_602_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_maxFVar_603_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_proofInstInfo_604_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_proofInstInfoFVar_605_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_inferType_606_);
lean_ctor_set(v_reuseFailAlloc_631_, 5, v_getLevel_607_);
lean_ctor_set(v_reuseFailAlloc_631_, 6, v_congrInfo_608_);
lean_ctor_set(v_reuseFailAlloc_631_, 7, v_defEqI_609_);
lean_ctor_set(v_reuseFailAlloc_631_, 8, v_extensions_610_);
lean_ctor_set(v_reuseFailAlloc_631_, 9, v_issues_611_);
lean_ctor_set(v_reuseFailAlloc_631_, 10, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_631_, 11, v_instanceOverrides_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*12, v_debug_613_);
v___x_626_ = v_reuseFailAlloc_631_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_st_ref_put(v_a_574_, v___x_626_);
if (v_isShared_599_ == 0)
{
v___x_629_ = v___x_598_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_596_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_570_);
return v___x_595_;
}
}
}
else
{
lean_object* v___x_636_; lean_object* v_canon_637_; lean_object* v_cacheInType_638_; lean_object* v___x_639_; 
v___x_636_ = lean_st_ref_get(v_a_574_);
v_canon_637_ = lean_ctor_get(v___x_636_, 10);
lean_inc_ref(v_canon_637_);
lean_dec(v___x_636_);
v_cacheInType_638_ = lean_ctor_get(v_canon_637_, 1);
lean_inc_ref(v_cacheInType_638_);
lean_dec_ref(v_canon_637_);
lean_inc_ref(v_e_570_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_580_, v___x_581_, v_cacheInType_638_, v_e_570_);
lean_dec_ref(v_cacheInType_638_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_k_571_);
lean_dec_ref(v_e_570_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 0);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_639_);
v___x_648_ = lean_box(v_a_572_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_649_ = lean_apply_8(v_k_571_, v___x_648_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, lean_box(0));
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_689_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_689_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_689_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_689_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v_canon_655_; lean_object* v_share_656_; lean_object* v_maxFVar_657_; lean_object* v_proofInstInfo_658_; lean_object* v_proofInstInfoFVar_659_; lean_object* v_inferType_660_; lean_object* v_getLevel_661_; lean_object* v_congrInfo_662_; lean_object* v_defEqI_663_; lean_object* v_extensions_664_; lean_object* v_issues_665_; lean_object* v_instanceOverrides_666_; uint8_t v_debug_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_688_; 
v___x_654_ = lean_st_ref_take(v_a_574_);
v_canon_655_ = lean_ctor_get(v___x_654_, 10);
v_share_656_ = lean_ctor_get(v___x_654_, 0);
v_maxFVar_657_ = lean_ctor_get(v___x_654_, 1);
v_proofInstInfo_658_ = lean_ctor_get(v___x_654_, 2);
v_proofInstInfoFVar_659_ = lean_ctor_get(v___x_654_, 3);
v_inferType_660_ = lean_ctor_get(v___x_654_, 4);
v_getLevel_661_ = lean_ctor_get(v___x_654_, 5);
v_congrInfo_662_ = lean_ctor_get(v___x_654_, 6);
v_defEqI_663_ = lean_ctor_get(v___x_654_, 7);
v_extensions_664_ = lean_ctor_get(v___x_654_, 8);
v_issues_665_ = lean_ctor_get(v___x_654_, 9);
v_instanceOverrides_666_ = lean_ctor_get(v___x_654_, 11);
v_debug_667_ = lean_ctor_get_uint8(v___x_654_, sizeof(void*)*12);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_688_ == 0)
{
v___x_669_ = v___x_654_;
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_instanceOverrides_666_);
lean_inc(v_canon_655_);
lean_inc(v_issues_665_);
lean_inc(v_extensions_664_);
lean_inc(v_defEqI_663_);
lean_inc(v_congrInfo_662_);
lean_inc(v_getLevel_661_);
lean_inc(v_inferType_660_);
lean_inc(v_proofInstInfoFVar_659_);
lean_inc(v_proofInstInfo_658_);
lean_inc(v_maxFVar_657_);
lean_inc(v_share_656_);
lean_dec(v___x_654_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_cache_671_; lean_object* v_cacheInType_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_687_; 
v_cache_671_ = lean_ctor_get(v_canon_655_, 0);
v_cacheInType_672_ = lean_ctor_get(v_canon_655_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_canon_655_);
if (v_isSharedCheck_687_ == 0)
{
v___x_674_ = v_canon_655_;
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_cacheInType_672_);
lean_inc(v_cache_671_);
lean_dec(v_canon_655_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_a_650_);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_580_, v___x_581_, v_cacheInType_672_, v_e_570_, v_a_650_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_cache_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 10, v___x_678_);
v___x_680_ = v___x_669_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_share_656_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_maxFVar_657_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_proofInstInfo_658_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_proofInstInfoFVar_659_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_inferType_660_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v_getLevel_661_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_congrInfo_662_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_defEqI_663_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_extensions_664_);
lean_ctor_set(v_reuseFailAlloc_685_, 9, v_issues_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 10, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 11, v_instanceOverrides_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*12, v_debug_667_);
v___x_680_ = v_reuseFailAlloc_685_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = lean_st_ref_put(v_a_574_, v___x_680_);
if (v_isShared_653_ == 0)
{
v___x_683_ = v___x_652_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_650_);
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
}
else
{
lean_dec_ref(v_e_570_);
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_690_, lean_object* v_k_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
uint8_t v_a_boxed_700_; lean_object* v_res_701_; 
v_a_boxed_700_ = lean_unbox(v_a_692_);
v_res_701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_690_, v_k_691_, v_a_boxed_700_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = l_Lean_Expr_cleanupAnnotations(v_e_708_);
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_711_ = l_Lean_Expr_isConstOf(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_isApp(v___x_709_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_709_);
return v___x_712_;
}
else
{
lean_object* v_arg_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_arg_713_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_arg_713_);
v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_709_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_dec_ref(v___x_714_);
lean_dec_ref(v_arg_713_);
return v___x_715_;
}
else
{
lean_object* v_arg_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_arg_716_ = lean_ctor_get(v___x_714_, 1);
lean_inc_ref(v_arg_716_);
v___x_717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_718_ = l_Lean_Expr_isApp(v___x_717_);
if (v___x_718_ == 0)
{
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_713_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_Lean_Expr_appFnCleanup___redArg(v___x_717_);
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_721_ = l_Lean_Expr_isConstOf(v___x_719_, v___x_720_);
lean_dec_ref(v___x_719_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_713_);
return v___x_721_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Expr_isBoolTrue(v_arg_716_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_arg_713_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_isBoolTrue(v_arg_713_);
return v___x_723_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_709_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = l_Lean_Expr_cleanupAnnotations(v_e_730_);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_733_ = l_Lean_Expr_isConstOf(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_734_ == 0)
{
lean_dec_ref(v___x_731_);
return v___x_734_;
}
else
{
lean_object* v_arg_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_arg_735_ = lean_ctor_get(v___x_731_, 1);
lean_inc_ref(v_arg_735_);
v___x_736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_737_ = l_Lean_Expr_isApp(v___x_736_);
if (v___x_737_ == 0)
{
lean_dec_ref(v___x_736_);
lean_dec_ref(v_arg_735_);
return v___x_737_;
}
else
{
lean_object* v_arg_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_arg_738_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_arg_738_);
v___x_739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_736_);
v___x_740_ = l_Lean_Expr_isApp(v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v___x_739_);
lean_dec_ref(v_arg_738_);
lean_dec_ref(v_arg_735_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_739_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_743_ = l_Lean_Expr_isConstOf(v___x_741_, v___x_742_);
lean_dec_ref(v___x_741_);
if (v___x_743_ == 0)
{
lean_dec_ref(v_arg_738_);
lean_dec_ref(v_arg_735_);
return v___x_743_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Expr_isBoolFalse(v_arg_738_);
if (v___x_744_ == 0)
{
lean_dec_ref(v_arg_735_);
return v___x_744_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Expr_isBoolTrue(v_arg_735_);
return v___x_745_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_731_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t v_x_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(v_x_749_);
v___x_751_ = lean_obj_tag_nat(v___x_750_);
lean_dec(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object* v_x_752_){
_start:
{
uint8_t v_x_4__boxed_753_; lean_object* v_res_754_; 
v_x_4__boxed_753_ = lean_unbox(v_x_752_);
v_res_754_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_4__boxed_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_755_){
_start:
{
lean_inc(v_k_755_);
return v_k_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_756_);
lean_dec(v_k_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_758_, lean_object* v_ctorIdx_759_, uint8_t v_t_760_, lean_object* v_h_761_, lean_object* v_k_762_){
_start:
{
lean_inc(v_k_762_);
return v_k_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_763_, lean_object* v_ctorIdx_764_, lean_object* v_t_765_, lean_object* v_h_766_, lean_object* v_k_767_){
_start:
{
uint8_t v_t_boxed_768_; lean_object* v_res_769_; 
v_t_boxed_768_ = lean_unbox(v_t_765_);
v_res_769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_763_, v_ctorIdx_764_, v_t_boxed_768_, v_h_766_, v_k_767_);
lean_dec(v_k_767_);
lean_dec(v_ctorIdx_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_770_){
_start:
{
lean_inc(v_canonType_770_);
return v_canonType_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_771_);
lean_dec(v_canonType_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_773_, uint8_t v_t_774_, lean_object* v_h_775_, lean_object* v_canonType_776_){
_start:
{
lean_inc(v_canonType_776_);
return v_canonType_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_777_, lean_object* v_t_778_, lean_object* v_h_779_, lean_object* v_canonType_780_){
_start:
{
uint8_t v_t_boxed_781_; lean_object* v_res_782_; 
v_t_boxed_781_ = lean_unbox(v_t_778_);
v_res_782_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_777_, v_t_boxed_781_, v_h_779_, v_canonType_780_);
lean_dec(v_canonType_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_783_){
_start:
{
lean_inc(v_canonInst_783_);
return v_canonInst_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_784_);
lean_dec(v_canonInst_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_786_, uint8_t v_t_787_, lean_object* v_h_788_, lean_object* v_canonInst_789_){
_start:
{
lean_inc(v_canonInst_789_);
return v_canonInst_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_canonInst_793_){
_start:
{
uint8_t v_t_boxed_794_; lean_object* v_res_795_; 
v_t_boxed_794_ = lean_unbox(v_t_791_);
v_res_795_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_790_, v_t_boxed_794_, v_h_792_, v_canonInst_793_);
lean_dec(v_canonInst_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_796_){
_start:
{
lean_inc(v_canonImplicit_796_);
return v_canonImplicit_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_797_);
lean_dec(v_canonImplicit_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_799_, uint8_t v_t_800_, lean_object* v_h_801_, lean_object* v_canonImplicit_802_){
_start:
{
lean_inc(v_canonImplicit_802_);
return v_canonImplicit_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_803_, lean_object* v_t_804_, lean_object* v_h_805_, lean_object* v_canonImplicit_806_){
_start:
{
uint8_t v_t_boxed_807_; lean_object* v_res_808_; 
v_t_boxed_807_ = lean_unbox(v_t_804_);
v_res_808_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_803_, v_t_boxed_807_, v_h_805_, v_canonImplicit_806_);
lean_dec(v_canonImplicit_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_809_){
_start:
{
lean_inc(v_visit_809_);
return v_visit_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_810_);
lean_dec(v_visit_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_812_, uint8_t v_t_813_, lean_object* v_h_814_, lean_object* v_visit_815_){
_start:
{
lean_inc(v_visit_815_);
return v_visit_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_816_, lean_object* v_t_817_, lean_object* v_h_818_, lean_object* v_visit_819_){
_start:
{
uint8_t v_t_boxed_820_; lean_object* v_res_821_; 
v_t_boxed_820_ = lean_unbox(v_t_817_);
v_res_821_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_816_, v_t_boxed_820_, v_h_818_, v_visit_819_);
lean_dec(v_visit_819_);
return v_res_821_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_822_; 
v___x_822_ = 0;
return v___x_822_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = 0;
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_836_, lean_object* v_x_837_){
_start:
{
switch(v_r_836_)
{
case 0:
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_838_;
}
case 1:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_839_;
}
case 2:
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_840_;
}
default: 
{
lean_object* v___x_841_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_r_boxed_844_; lean_object* v_res_845_; 
v_r_boxed_844_ = lean_unbox(v_r_842_);
v_res_845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_844_, v_x_843_);
lean_dec(v_x_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_848_, lean_object* v_i_849_, lean_object* v_arg_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_pinfos_848_);
v___x_907_ = lean_nat_dec_lt(v_i_849_, v___x_906_);
if (v___x_907_ == 0)
{
v___y_857_ = v_a_851_;
v___y_858_ = v_a_852_;
v___y_859_ = v_a_853_;
v___y_860_ = v_a_854_;
goto v___jp_856_;
}
else
{
lean_object* v_pinfo_908_; uint8_t v_isInstance_909_; 
v_pinfo_908_ = lean_array_fget_borrowed(v_pinfos_848_, v_i_849_);
v_isInstance_909_ = lean_ctor_get_uint8(v_pinfo_908_, sizeof(void*)*1 + 4);
if (v_isInstance_909_ == 0)
{
uint8_t v_isProp_910_; 
v_isProp_910_ = lean_ctor_get_uint8(v_pinfo_908_, sizeof(void*)*1 + 2);
if (v_isProp_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_908_);
if (v___x_911_ == 0)
{
v___y_857_ = v_a_851_;
v___y_858_ = v_a_852_;
v___y_859_ = v_a_853_;
v___y_860_ = v_a_854_;
goto v___jp_856_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_isTypeFormer(v_arg_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_928_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_928_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_928_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_928_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
uint8_t v___x_917_; 
v___x_917_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_918_ = 2;
v___x_919_ = lean_box(v___x_918_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_919_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = 0;
v___x_924_ = lean_box(v___x_923_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_924_);
v___x_926_ = v___x_915_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_912_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_912_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
else
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_arg_850_);
v___x_937_ = 3;
v___x_938_ = lean_box(v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
else
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_arg_850_);
v___x_940_ = 1;
v___x_941_ = lean_box(v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
v___jp_856_:
{
lean_object* v___x_861_; 
lean_inc_ref(v_arg_850_);
v___x_861_ = l_Lean_Meta_isProp(v_arg_850_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_897_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_897_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_897_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_897_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_del_object(v___x_864_);
v___x_867_ = l_Lean_Meta_isTypeFormer(v_arg_850_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_883_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_883_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_883_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; 
v___x_872_ = lean_unbox(v_a_868_);
lean_dec(v_a_868_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = 3;
v___x_874_ = lean_box(v___x_873_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = 0;
v___x_879_ = lean_box(v___x_878_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_879_);
v___x_881_ = v___x_870_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
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
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v_a_884_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_867_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_867_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
lean_dec_ref(v_arg_850_);
v___x_892_ = 3;
v___x_893_ = lean_box(v___x_892_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_893_);
v___x_895_ = v___x_864_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v_arg_850_);
v_a_898_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_861_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_861_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_943_, lean_object* v_i_944_, lean_object* v_arg_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_943_, v_i_944_, v_arg_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_i_944_);
lean_dec_ref(v_pinfos_943_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_952_, lean_object* v_offset_953_){
_start:
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_nat_dec_eq(v_offset_953_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l_Lean_mkNatLit(v_offset_953_);
v___x_957_ = l_Lean_mkNatAdd(v_e_952_, v___x_956_);
return v___x_957_;
}
else
{
lean_dec(v_offset_953_);
return v_e_952_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_958_; lean_object* v_dummy_959_; 
v___x_958_ = lean_box(0);
v_dummy_959_ = l_Lean_Expr_sort___override(v___x_958_);
return v_dummy_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_960_, lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
uint8_t v_fromClass_967_; 
v_fromClass_967_ = lean_ctor_get_uint8(v_info_960_, sizeof(void*)*3);
if (v_fromClass_967_ == 0)
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_961_, v_fromClass_967_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1004_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_1004_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1004_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
if (lean_obj_tag(v_a_969_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_del_object(v___x_971_);
v_val_973_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v_a_969_, 1);
v___x_974_ = l_Lean_Expr_getAppFn(v_val_973_);
v___x_975_ = l_Lean_Meta_reduceProj_x3f(v___x_974_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
if (lean_obj_tag(v_a_976_) == 0)
{
lean_dec(v_val_973_);
return v___x_975_;
}
else
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_998_; 
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_999_);
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_998_;
goto v_resetjp_977_;
}
else
{
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_998_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_val_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_997_; 
v_val_980_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_997_ == 0)
{
v___x_982_ = v_a_976_;
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_val_980_);
lean_dec(v_a_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_dummy_984_; lean_object* v_nargs_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_dummy_984_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_985_ = l_Lean_Expr_getAppNumArgs(v_val_973_);
lean_inc(v_nargs_985_);
v___x_986_ = lean_mk_array(v_nargs_985_, v_dummy_984_);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_sub(v_nargs_985_, v___x_987_);
lean_dec(v_nargs_985_);
v___x_989_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_973_, v___x_986_, v___x_988_);
v___x_990_ = l_Lean_mkAppN(v_val_980_, v___x_989_);
lean_dec_ref(v___x_989_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_990_);
v___x_992_ = v___x_982_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_996_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_992_);
v___x_994_ = v___x_978_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
else
{
lean_dec(v_val_973_);
return v___x_975_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec(v_a_969_);
v___x_1000_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_1000_);
v___x_1002_ = v___x_971_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
return v___x_968_;
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_e_961_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_1007_, lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_1007_, v_e_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec_ref(v_info_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_1015_, lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_1015_, v_e_1016_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_1025_, lean_object* v_e_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_1025_, v_e_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_info_1025_);
return v_res_1034_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_1035_){
_start:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_1037_ = l_Lean_Expr_isConstOf(v_e_1035_, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_1038_){
_start:
{
uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_res_1039_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_1038_);
lean_dec_ref(v_e_1038_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = l_Lean_Expr_cleanupAnnotations(v_e_1074_);
v___x_1076_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_1077_ = l_Lean_Expr_isConstOf(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Lean_Expr_isApp(v___x_1075_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v___x_1075_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1075_);
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_1081_ = l_Lean_Expr_isConstOf(v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_Expr_isApp(v___x_1079_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v___x_1079_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1079_);
v___x_1084_ = l_Lean_Expr_isApp(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1083_);
v___x_1086_ = l_Lean_Expr_isApp(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1085_);
v___x_1088_ = l_Lean_Expr_isApp(v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1087_);
v___x_1090_ = l_Lean_Expr_isApp(v___x_1089_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v___x_1089_);
return v___x_1090_;
}
else
{
lean_object* v_arg_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_arg_1091_ = lean_ctor_get(v___x_1089_, 1);
lean_inc_ref(v_arg_1091_);
v___x_1092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1089_);
v___x_1093_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1094_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1096_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1098_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1100_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1102_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1101_);
lean_dec_ref(v___x_1092_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v_arg_1091_);
return v___x_1102_;
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1091_);
lean_dec_ref(v_arg_1091_);
return v___x_1103_;
}
}
else
{
uint8_t v___x_1104_; 
lean_dec_ref(v___x_1092_);
v___x_1104_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1091_);
lean_dec_ref(v_arg_1091_);
return v___x_1104_;
}
}
else
{
uint8_t v___x_1105_; 
lean_dec_ref(v___x_1092_);
v___x_1105_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1091_);
lean_dec_ref(v_arg_1091_);
return v___x_1105_;
}
}
else
{
uint8_t v___x_1106_; 
lean_dec_ref(v___x_1092_);
v___x_1106_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1091_);
lean_dec_ref(v_arg_1091_);
return v___x_1106_;
}
}
else
{
uint8_t v___x_1107_; 
lean_dec_ref(v___x_1092_);
v___x_1107_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1091_);
lean_dec_ref(v_arg_1091_);
return v___x_1107_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1079_);
return v___x_1081_;
}
}
}
else
{
lean_dec_ref(v___x_1075_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1108_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1117_, lean_object* v_inst_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
lean_inc_ref(v_inst_1118_);
lean_inc_ref(v_e_1117_);
v___x_1126_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1117_, v_inst_1118_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1177_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1177_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1177_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1129_);
v___x_1132_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1117_);
v___x_1133_ = l_Lean_indentExpr(v_e_1117_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_indentExpr(v_inst_1118_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1119_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1165_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1165_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1165_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v_verbose_1144_; 
v_verbose_1144_ = lean_ctor_get_uint8(v_a_1140_, 0);
lean_dec(v_a_1140_);
if (v_verbose_1144_ == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref_known(v___x_1138_, 2);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_e_1117_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_e_1117_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
lean_object* v___x_1148_; 
lean_del_object(v___x_1142_);
v___x_1148_ = l_Lean_Meta_Sym_reportIssue(v___x_1138_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v___x_1148_, 0);
lean_dec(v_unused_1156_);
v___x_1150_ = v___x_1148_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v___x_1148_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_e_1117_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_e_1117_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_e_1117_);
v_a_1157_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1148_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1148_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref_known(v___x_1138_, 2);
lean_dec_ref(v_e_1117_);
v_a_1166_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1139_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1139_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v___x_1175_; 
lean_dec_ref(v_e_1117_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_inst_1118_);
v___x_1175_ = v___x_1129_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_inst_1118_);
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
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_inst_1118_);
lean_dec_ref(v_e_1117_);
v_a_1178_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1126_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1126_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1186_, lean_object* v_inst_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1186_, v_inst_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 0;
return v___x_1198_;
}
else
{
lean_object* v_key_1199_; lean_object* v_tail_1200_; uint8_t v___x_1201_; 
v_key_1199_ = lean_ctor_get(v_x_1197_, 0);
v_tail_1200_ = lean_ctor_get(v_x_1197_, 2);
v___x_1201_ = lean_expr_eqv(v_key_1199_, v_a_1196_);
if (v___x_1201_ == 0)
{
v_x_1197_ = v_tail_1200_;
goto _start;
}
else
{
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1203_, lean_object* v_x_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1203_, v_x_1204_);
lean_dec(v_x_1204_);
lean_dec_ref(v_a_1203_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35___redArg(lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
return v_x_1207_;
}
else
{
lean_object* v_key_1209_; lean_object* v_value_1210_; lean_object* v_tail_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1234_; 
v_key_1209_ = lean_ctor_get(v_x_1208_, 0);
v_value_1210_ = lean_ctor_get(v_x_1208_, 1);
v_tail_1211_ = lean_ctor_get(v_x_1208_, 2);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1213_ = v_x_1208_;
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_tail_1211_);
lean_inc(v_value_1210_);
lean_inc(v_key_1209_);
lean_dec(v_x_1208_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; uint64_t v___x_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; uint64_t v_fold_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1215_ = lean_array_get_size(v_x_1207_);
v___x_1216_ = l_Lean_Expr_hash(v_key_1209_);
v___x_1217_ = 32ULL;
v___x_1218_ = lean_uint64_shift_right(v___x_1216_, v___x_1217_);
v_fold_1219_ = lean_uint64_xor(v___x_1216_, v___x_1218_);
v___x_1220_ = 16ULL;
v___x_1221_ = lean_uint64_shift_right(v_fold_1219_, v___x_1220_);
v___x_1222_ = lean_uint64_xor(v_fold_1219_, v___x_1221_);
v___x_1223_ = lean_uint64_to_usize(v___x_1222_);
v___x_1224_ = lean_usize_of_nat(v___x_1215_);
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_sub(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_usize_land(v___x_1223_, v___x_1226_);
v___x_1228_ = lean_array_uget_borrowed(v_x_1207_, v___x_1227_);
lean_inc(v___x_1228_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v___x_1228_);
v___x_1230_ = v___x_1213_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_key_1209_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_value_1210_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_array_uset(v_x_1207_, v___x_1227_, v___x_1230_);
v_x_1207_ = v___x_1231_;
v_x_1208_ = v_tail_1211_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30___redArg(lean_object* v_i_1235_, lean_object* v_source_1236_, lean_object* v_target_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_array_get_size(v_source_1236_);
v___x_1239_ = lean_nat_dec_lt(v_i_1235_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v_source_1236_);
lean_dec(v_i_1235_);
return v_target_1237_;
}
else
{
lean_object* v_es_1240_; lean_object* v___x_1241_; lean_object* v_source_1242_; lean_object* v_target_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_es_1240_ = lean_array_fget(v_source_1236_, v_i_1235_);
v___x_1241_ = lean_box(0);
v_source_1242_ = lean_array_fset(v_source_1236_, v_i_1235_, v___x_1241_);
v_target_1243_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35___redArg(v_target_1237_, v_es_1240_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1235_, v___x_1244_);
lean_dec(v_i_1235_);
v_i_1235_ = v___x_1245_;
v_source_1236_ = v_source_1242_;
v_target_1237_ = v_target_1243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_nbuckets_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1248_ = lean_array_get_size(v_data_1247_);
v___x_1249_ = lean_unsigned_to_nat(2u);
v_nbuckets_1250_ = lean_nat_mul(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_mk_array(v_nbuckets_1250_, v___x_1252_);
v___x_1254_ = lean_array_propagate_mark(v_data_1247_, v___x_1253_);
v___x_1255_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30___redArg(v___x_1251_, v_data_1247_, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1256_, lean_object* v_b_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_dec(v_b_1257_);
lean_dec_ref(v_a_1256_);
return v_x_1258_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1273_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1263_ = v_x_1258_;
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_tail_1261_);
lean_inc(v_value_1260_);
lean_inc(v_key_1259_);
lean_dec(v_x_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_expr_eqv(v_key_1259_, v_a_1256_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1256_, v_b_1257_, v_tail_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 2, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_key_1259_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_value_1260_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
lean_object* v___x_1271_; 
lean_dec(v_value_1260_);
lean_dec(v_key_1259_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_b_1257_);
lean_ctor_set(v___x_1263_, 0, v_a_1256_);
v___x_1271_ = v___x_1263_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1256_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_b_1257_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_tail_1261_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_){
_start:
{
lean_object* v_size_1277_; lean_object* v_buckets_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1321_; 
v_size_1277_ = lean_ctor_get(v_m_1274_, 0);
v_buckets_1278_ = lean_ctor_get(v_m_1274_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_m_1274_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1280_ = v_m_1274_;
v_isShared_1281_ = v_isSharedCheck_1321_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_buckets_1278_);
lean_inc(v_size_1277_);
lean_dec(v_m_1274_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1321_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; uint64_t v_fold_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_bkt_1295_; uint8_t v___x_1296_; 
v___x_1282_ = lean_array_get_size(v_buckets_1278_);
v___x_1283_ = l_Lean_Expr_hash(v_a_1275_);
v___x_1284_ = 32ULL;
v___x_1285_ = lean_uint64_shift_right(v___x_1283_, v___x_1284_);
v_fold_1286_ = lean_uint64_xor(v___x_1283_, v___x_1285_);
v___x_1287_ = 16ULL;
v___x_1288_ = lean_uint64_shift_right(v_fold_1286_, v___x_1287_);
v___x_1289_ = lean_uint64_xor(v_fold_1286_, v___x_1288_);
v___x_1290_ = lean_uint64_to_usize(v___x_1289_);
v___x_1291_ = lean_usize_of_nat(v___x_1282_);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_sub(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_usize_land(v___x_1290_, v___x_1293_);
v_bkt_1295_ = lean_array_uget_borrowed(v_buckets_1278_, v___x_1294_);
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1275_, v_bkt_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v_size_x27_1298_; lean_object* v___x_1299_; lean_object* v_buckets_x27_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1297_ = lean_unsigned_to_nat(1u);
v_size_x27_1298_ = lean_nat_add(v_size_1277_, v___x_1297_);
lean_dec(v_size_1277_);
lean_inc(v_bkt_1295_);
v___x_1299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_a_1275_);
lean_ctor_set(v___x_1299_, 1, v_b_1276_);
lean_ctor_set(v___x_1299_, 2, v_bkt_1295_);
v_buckets_x27_1300_ = lean_array_uset(v_buckets_1278_, v___x_1294_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(4u);
v___x_1302_ = lean_nat_mul(v_size_x27_1298_, v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(3u);
v___x_1304_ = lean_nat_div(v___x_1302_, v___x_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_array_get_size(v_buckets_x27_1300_);
v___x_1306_ = lean_nat_dec_le(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
if (v___x_1306_ == 0)
{
lean_object* v_val_1307_; lean_object* v___x_1309_; 
v_val_1307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1300_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_val_1307_);
lean_ctor_set(v___x_1280_, 0, v_size_x27_1298_);
v___x_1309_ = v___x_1280_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_size_x27_1298_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_val_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v___x_1312_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_buckets_x27_1300_);
lean_ctor_set(v___x_1280_, 0, v_size_x27_1298_);
v___x_1312_ = v___x_1280_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_size_x27_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_buckets_x27_1300_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v_buckets_x27_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_bkt_1295_);
v___x_1314_ = lean_box(0);
v_buckets_x27_1315_ = lean_array_uset(v_buckets_1278_, v___x_1294_, v___x_1314_);
v___x_1316_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1275_, v_b_1276_, v_bkt_1295_);
v___x_1317_ = lean_array_uset(v_buckets_x27_1315_, v___x_1294_, v___x_1316_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1317_);
v___x_1319_ = v___x_1280_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_size_1277_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0(lean_object* v_k_1322_, uint8_t v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_box(v___y_1323_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
v___x_1333_ = lean_apply_9(v_k_1322_, v_b_1326_, v___x_1332_, v___y_1324_, v___y_1325_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, lean_box(0));
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0___boxed(lean_object* v_k_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___y_64386__boxed_1344_; lean_object* v_res_1345_; 
v___y_64386__boxed_1344_ = lean_unbox(v___y_1335_);
v_res_1345_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0(v_k_1334_, v___y_64386__boxed_1344_, v___y_1336_, v___y_1337_, v_b_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(lean_object* v_name_1346_, uint8_t v_bi_1347_, lean_object* v_type_1348_, lean_object* v_k_1349_, uint8_t v_kind_1350_, uint8_t v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_box(v___y_1351_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1360_, 0, v_k_1349_);
lean_closure_set(v___f_1360_, 1, v___x_1359_);
lean_closure_set(v___f_1360_, 2, v___y_1352_);
lean_closure_set(v___f_1360_, 3, v___y_1353_);
v___x_1361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1346_, v_bi_1347_, v_type_1348_, v___f_1360_, v_kind_1350_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg___boxed(lean_object* v_name_1370_, lean_object* v_bi_1371_, lean_object* v_type_1372_, lean_object* v_k_1373_, lean_object* v_kind_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_bi_boxed_1383_; uint8_t v_kind_boxed_1384_; uint8_t v___y_64414__boxed_1385_; lean_object* v_res_1386_; 
v_bi_boxed_1383_ = lean_unbox(v_bi_1371_);
v_kind_boxed_1384_ = lean_unbox(v_kind_1374_);
v___y_64414__boxed_1385_ = lean_unbox(v___y_1375_);
v_res_1386_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(v_name_1370_, v_bi_boxed_1383_, v_type_1372_, v_k_1373_, v_kind_boxed_1384_, v___y_64414__boxed_1385_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v_env_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1390_ = lean_st_ref_get(v___y_1388_);
v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_ref(v_env_1391_);
lean_dec(v___x_1390_);
v___x_1392_ = l_Lean_Meta_isMatcherCore(v_env_1391_, v_declName_1387_);
v___x_1393_ = lean_box(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1395_, v___y_1396_);
lean_dec(v___y_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v_env_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_st_ref_get(v___y_1400_);
v_env_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc_ref(v_env_1403_);
lean_dec(v___x_1402_);
v___x_1404_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1403_, v_declName_1399_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1406_, v___y_1407_);
lean_dec(v___y_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v_env_1417_; uint8_t v___x_1418_; lean_object* v_env_1419_; lean_object* v___x_1420_; lean_object* v_toCold_1421_; lean_object* v_mctx_1422_; lean_object* v_lctx_1423_; lean_object* v_options_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1416_ = lean_st_ref_get(v___y_1414_);
v_env_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_env_1417_);
lean_dec(v___x_1416_);
v___x_1418_ = 0;
v_env_1419_ = l_Lean_Environment_setRecordingDeps(v_env_1417_, v___x_1418_);
v___x_1420_ = lean_st_ref_get(v___y_1412_);
v_toCold_1421_ = lean_ctor_get(v___y_1413_, 0);
v_mctx_1422_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_ref(v_mctx_1422_);
lean_dec(v___x_1420_);
v_lctx_1423_ = lean_ctor_get(v___y_1411_, 2);
v_options_1424_ = lean_ctor_get(v_toCold_1421_, 2);
lean_inc_ref(v_options_1424_);
lean_inc_ref(v_lctx_1423_);
v___x_1425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1425_, 0, v_env_1419_);
lean_ctor_set(v___x_1425_, 1, v_mctx_1422_);
lean_ctor_set(v___x_1425_, 2, v_lctx_1423_);
lean_ctor_set(v___x_1425_, 3, v_options_1424_);
v___x_1426_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_msgData_1410_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1435_; double v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_float_of_nat(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1494_; 
v_ref_1447_ = lean_ctor_get(v___y_1444_, 2);
v___x_1448_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1494_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1494_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_traceState_1454_; lean_object* v_env_1455_; lean_object* v_nextMacroScope_1456_; lean_object* v_ngen_1457_; lean_object* v_auxDeclNGen_1458_; lean_object* v_cache_1459_; lean_object* v_recordedDeps_1460_; lean_object* v_messages_1461_; lean_object* v_infoState_1462_; lean_object* v_snapshotTasks_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1493_; 
v___x_1453_ = lean_st_ref_take(v___y_1445_);
v_traceState_1454_ = lean_ctor_get(v___x_1453_, 4);
v_env_1455_ = lean_ctor_get(v___x_1453_, 0);
v_nextMacroScope_1456_ = lean_ctor_get(v___x_1453_, 1);
v_ngen_1457_ = lean_ctor_get(v___x_1453_, 2);
v_auxDeclNGen_1458_ = lean_ctor_get(v___x_1453_, 3);
v_cache_1459_ = lean_ctor_get(v___x_1453_, 5);
v_recordedDeps_1460_ = lean_ctor_get(v___x_1453_, 6);
v_messages_1461_ = lean_ctor_get(v___x_1453_, 7);
v_infoState_1462_ = lean_ctor_get(v___x_1453_, 8);
v_snapshotTasks_1463_ = lean_ctor_get(v___x_1453_, 9);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1465_ = v___x_1453_;
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_snapshotTasks_1463_);
lean_inc(v_infoState_1462_);
lean_inc(v_messages_1461_);
lean_inc(v_recordedDeps_1460_);
lean_inc(v_cache_1459_);
lean_inc(v_traceState_1454_);
lean_inc(v_auxDeclNGen_1458_);
lean_inc(v_ngen_1457_);
lean_inc(v_nextMacroScope_1456_);
lean_inc(v_env_1455_);
lean_dec(v___x_1453_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint64_t v_tid_1467_; lean_object* v_traces_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1492_; 
v_tid_1467_ = lean_ctor_get_uint64(v_traceState_1454_, sizeof(void*)*1);
v_traces_1468_ = lean_ctor_get(v_traceState_1454_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_traceState_1454_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1470_ = v_traceState_1454_;
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_traces_1468_);
lean_dec(v_traceState_1454_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; double v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1475_ = 0;
v___x_1476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1477_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1477_, 0, v_cls_1440_);
lean_ctor_set(v___x_1477_, 1, v___x_1473_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_ctor_set_float(v___x_1477_, sizeof(void*)*3, v___x_1474_);
lean_ctor_set_float(v___x_1477_, sizeof(void*)*3 + 8, v___x_1474_);
lean_ctor_set_uint8(v___x_1477_, sizeof(void*)*3 + 16, v___x_1475_);
v___x_1478_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1479_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v_a_1449_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
lean_inc(v_ref_1447_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_ref_1447_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Lean_PersistentArray_push___redArg(v_traces_1468_, v___x_1480_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1481_);
v___x_1483_ = v___x_1470_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1481_);
lean_ctor_set_uint64(v_reuseFailAlloc_1491_, sizeof(void*)*1, v_tid_1467_);
v___x_1483_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v___x_1483_);
v___x_1485_ = v___x_1465_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_env_1455_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_nextMacroScope_1456_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_ngen_1457_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_auxDeclNGen_1458_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_cache_1459_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_recordedDeps_1460_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_messages_1461_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_infoState_1462_);
lean_ctor_set(v_reuseFailAlloc_1490_, 9, v_snapshotTasks_1463_);
v___x_1485_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_st_ref_put(v___y_1445_, v___x_1485_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1472_);
v___x_1488_ = v___x_1451_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1472_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1495_, lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1495_, v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1503_, lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
else
{
lean_object* v_key_1506_; lean_object* v_value_1507_; lean_object* v_tail_1508_; uint8_t v___x_1509_; 
v_key_1506_ = lean_ctor_get(v_x_1504_, 0);
v_value_1507_ = lean_ctor_get(v_x_1504_, 1);
v_tail_1508_ = lean_ctor_get(v_x_1504_, 2);
v___x_1509_ = lean_expr_eqv(v_key_1506_, v_a_1503_);
if (v___x_1509_ == 0)
{
v_x_1504_ = v_tail_1508_;
goto _start;
}
else
{
lean_object* v___x_1511_; 
lean_inc(v_value_1507_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_value_1507_);
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1512_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_buckets_1517_; lean_object* v___x_1518_; uint64_t v___x_1519_; uint64_t v___x_1520_; uint64_t v___x_1521_; uint64_t v_fold_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_buckets_1517_ = lean_ctor_get(v_m_1515_, 1);
v___x_1518_ = lean_array_get_size(v_buckets_1517_);
v___x_1519_ = l_Lean_Expr_hash(v_a_1516_);
v___x_1520_ = 32ULL;
v___x_1521_ = lean_uint64_shift_right(v___x_1519_, v___x_1520_);
v_fold_1522_ = lean_uint64_xor(v___x_1519_, v___x_1521_);
v___x_1523_ = 16ULL;
v___x_1524_ = lean_uint64_shift_right(v_fold_1522_, v___x_1523_);
v___x_1525_ = lean_uint64_xor(v_fold_1522_, v___x_1524_);
v___x_1526_ = lean_uint64_to_usize(v___x_1525_);
v___x_1527_ = lean_usize_of_nat(v___x_1518_);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_sub(v___x_1527_, v___x_1528_);
v___x_1530_ = lean_usize_land(v___x_1526_, v___x_1529_);
v___x_1531_ = lean_array_uget_borrowed(v_buckets_1517_, v___x_1530_);
v___x_1532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1516_, v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1533_, v_a_1534_);
lean_dec_ref(v_a_1534_);
lean_dec_ref(v_m_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg(lean_object* v_name_1536_, lean_object* v_type_1537_, lean_object* v_val_1538_, lean_object* v_k_1539_, uint8_t v_nondep_1540_, uint8_t v_kind_1541_, uint8_t v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_box(v___y_1542_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1551_, 0, v_k_1539_);
lean_closure_set(v___f_1551_, 1, v___x_1550_);
lean_closure_set(v___f_1551_, 2, v___y_1543_);
lean_closure_set(v___f_1551_, 3, v___y_1544_);
v___x_1552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1536_, v_type_1537_, v_val_1538_, v___f_1551_, v_nondep_1540_, v_kind_1541_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1552_) == 0)
{
return v___x_1552_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg___boxed(lean_object* v_name_1561_, lean_object* v_type_1562_, lean_object* v_val_1563_, lean_object* v_k_1564_, lean_object* v_nondep_1565_, lean_object* v_kind_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_nondep_boxed_1575_; uint8_t v_kind_boxed_1576_; uint8_t v___y_64663__boxed_1577_; lean_object* v_res_1578_; 
v_nondep_boxed_1575_ = lean_unbox(v_nondep_1565_);
v_kind_boxed_1576_ = lean_unbox(v_kind_1566_);
v___y_64663__boxed_1577_ = lean_unbox(v___y_1567_);
v_res_1578_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg(v_name_1561_, v_type_1562_, v_val_1563_, v_k_1564_, v_nondep_boxed_1575_, v_kind_boxed_1576_, v___y_64663__boxed_1577_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = l_Lean_instInhabitedExpr;
v___x_1581_ = lean_panic_fn_borrowed(v___x_1580_, v_msg_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1582_, lean_object* v_body_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___y_64842__boxed_1593_; lean_object* v_res_1594_; 
v___y_64842__boxed_1593_ = lean_unbox(v___y_1585_);
v_res_1594_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1582_, v_body_1583_, v_x_1584_, v___y_64842__boxed_1593_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1597_, lean_object* v_body_1598_, lean_object* v_x_1599_, uint8_t v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_array_push(v_fvars_1597_, v_x_1599_);
v___x_1609_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1608_, v_body_1598_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1610_, lean_object* v_body_1611_, lean_object* v_x_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___y_64853__boxed_1621_; lean_object* v_res_1622_; 
v___y_64853__boxed_1621_ = lean_unbox(v___y_1613_);
v_res_1622_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1610_, v_body_1611_, v_x_1612_, v___y_64853__boxed_1621_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1623_, lean_object* v_e_1624_, uint8_t v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
if (lean_obj_tag(v_e_1624_) == 6)
{
lean_object* v_binderName_1633_; lean_object* v_binderType_1634_; lean_object* v_body_1635_; uint8_t v_binderInfo_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_binderName_1633_ = lean_ctor_get(v_e_1624_, 0);
lean_inc(v_binderName_1633_);
v_binderType_1634_ = lean_ctor_get(v_e_1624_, 1);
lean_inc_ref(v_binderType_1634_);
v_body_1635_ = lean_ctor_get(v_e_1624_, 2);
lean_inc_ref(v_body_1635_);
v_binderInfo_1636_ = lean_ctor_get_uint8(v_e_1624_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1624_, 3);
lean_inc_ref(v_fvars_1623_);
v___f_1637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1637_, 0, v_fvars_1623_);
lean_closure_set(v___f_1637_, 1, v_body_1635_);
v___x_1638_ = lean_expr_instantiate_rev(v_binderType_1634_, v_fvars_1623_);
lean_dec_ref(v_fvars_1623_);
lean_dec_ref(v_binderType_1634_);
v___x_1639_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1638_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(v_binderName_1633_, v_binderInfo_1636_, v_a_1640_, v___f_1637_, v___x_1641_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
return v___x_1642_;
}
else
{
lean_dec_ref(v___f_1637_);
lean_dec(v_binderName_1633_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_expr_instantiate_rev(v_e_1624_, v_fvars_1623_);
lean_dec_ref(v_e_1624_);
v___x_1644_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1643_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; uint8_t v___x_1646_; uint8_t v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = 0;
v___x_1647_ = 1;
v___x_1648_ = 1;
v___x_1649_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1623_, v_a_1645_, v___x_1646_, v___x_1647_, v___x_1646_, v___x_1647_, v___x_1648_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec_ref(v_fvars_1623_);
return v___x_1649_;
}
else
{
lean_dec_ref(v_fvars_1623_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1650_, uint8_t v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
if (v_a_1651_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1659_, v_e_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1662_ = l_Lean_Meta_Sym_etaReduce(v_e_1650_);
lean_dec_ref(v_e_1650_);
v___x_1663_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1661_, v___x_1662_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1664_, lean_object* v_body_1665_, lean_object* v_x_1666_, uint8_t v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_array_push(v_fvars_1664_, v_x_1666_);
v___x_1676_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1675_, v_body_1665_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1677_, lean_object* v_body_1678_, lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v___y_64864__boxed_1688_; lean_object* v_res_1689_; 
v___y_64864__boxed_1688_ = lean_unbox(v___y_1680_);
v_res_1689_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1677_, v_body_1678_, v_x_1679_, v___y_64864__boxed_1688_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1690_, lean_object* v_e_1691_, uint8_t v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
if (lean_obj_tag(v_e_1691_) == 8)
{
lean_object* v_declName_1700_; lean_object* v_type_1701_; lean_object* v_value_1702_; lean_object* v_body_1703_; uint8_t v_nondep_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_declName_1700_ = lean_ctor_get(v_e_1691_, 0);
lean_inc(v_declName_1700_);
v_type_1701_ = lean_ctor_get(v_e_1691_, 1);
lean_inc_ref(v_type_1701_);
v_value_1702_ = lean_ctor_get(v_e_1691_, 2);
lean_inc_ref(v_value_1702_);
v_body_1703_ = lean_ctor_get(v_e_1691_, 3);
lean_inc_ref(v_body_1703_);
v_nondep_1704_ = lean_ctor_get_uint8(v_e_1691_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1691_, 4);
lean_inc_ref(v_fvars_1690_);
v___f_1705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1705_, 0, v_fvars_1690_);
lean_closure_set(v___f_1705_, 1, v_body_1703_);
v___x_1706_ = lean_expr_instantiate_rev(v_type_1701_, v_fvars_1690_);
lean_dec_ref(v_type_1701_);
v___x_1707_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1706_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = lean_expr_instantiate_rev(v_value_1702_, v_fvars_1690_);
lean_dec_ref(v_fvars_1690_);
lean_dec_ref(v_value_1702_);
v___x_1710_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1709_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = 0;
v___x_1713_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg(v_declName_1700_, v_a_1708_, v_a_1711_, v___f_1705_, v_nondep_1704_, v___x_1712_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
return v___x_1713_;
}
else
{
lean_dec(v_a_1708_);
lean_dec_ref(v___f_1705_);
lean_dec(v_declName_1700_);
return v___x_1710_;
}
}
else
{
lean_dec_ref(v___f_1705_);
lean_dec_ref(v_value_1702_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_fvars_1690_);
return v___x_1707_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_expr_instantiate_rev(v_e_1691_, v_fvars_1690_);
lean_dec_ref(v_e_1691_);
v___x_1715_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1714_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; uint8_t v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; lean_object* v___x_1720_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1717_ = 1;
v___x_1718_ = 0;
v___x_1719_ = 1;
v___x_1720_ = l_Lean_Meta_mkLetFVars(v_fvars_1690_, v_a_1716_, v___x_1717_, v___x_1718_, v___x_1719_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec_ref(v_fvars_1690_);
return v___x_1720_;
}
else
{
lean_dec_ref(v_fvars_1690_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1721_, uint8_t v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
if (v_a_1722_ == 0)
{
uint8_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = 1;
v___x_1731_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1721_, v___x_1730_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
return v___x_1732_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1736_, lean_object* v_type_1737_, uint8_t v_report_1738_, uint8_t v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___x_1797_; 
lean_inc_ref(v_type_1737_);
v___x_1797_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1737_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
if (lean_obj_tag(v_a_1798_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v_type_1737_);
v_val_1799_ = lean_ctor_get(v_a_1798_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v_a_1798_, 1);
v___x_1800_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1736_, v_val_1799_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; 
lean_dec(v_a_1798_);
v___x_1801_ = l_Lean_Expr_getAppFn(v_e_1736_);
if (lean_obj_tag(v___x_1801_) == 4)
{
lean_object* v_declName_1802_; lean_object* v___x_1803_; 
v_declName_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_declName_1802_);
lean_dec_ref_known(v___x_1801_, 2);
v___x_1803_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1802_, v_a_1745_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_object* v_val_1805_; uint8_t v___x_1806_; 
v_val_1805_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v_a_1804_, 1);
v___x_1806_ = l_Lean_Expr_isApp(v_e_1736_);
if (v___x_1806_ == 0)
{
lean_dec(v_val_1805_);
v___y_1748_ = v_a_1740_;
v___y_1749_ = v_a_1741_;
v___y_1750_ = v_a_1742_;
v___y_1751_ = v_a_1743_;
v___y_1752_ = v_a_1744_;
v___y_1753_ = v_a_1745_;
goto v___jp_1747_;
}
else
{
uint8_t v_fromClass_1807_; 
v_fromClass_1807_ = lean_ctor_get_uint8(v_val_1805_, sizeof(void*)*3);
lean_dec(v_val_1805_);
if (v_fromClass_1807_ == 0)
{
v___y_1748_ = v_a_1740_;
v___y_1749_ = v_a_1741_;
v___y_1750_ = v_a_1742_;
v___y_1751_ = v_a_1743_;
v___y_1752_ = v_a_1744_;
v___y_1753_ = v_a_1745_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v_type_1737_);
v___x_1808_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_1736_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1808_;
}
}
}
else
{
lean_dec(v_a_1804_);
v___y_1748_ = v_a_1740_;
v___y_1749_ = v_a_1741_;
v___y_1750_ = v_a_1742_;
v___y_1751_ = v_a_1743_;
v___y_1752_ = v_a_1744_;
v___y_1753_ = v_a_1745_;
goto v___jp_1747_;
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_type_1737_);
lean_dec_ref(v_e_1736_);
v_a_1809_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1803_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1803_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_dec_ref(v___x_1801_);
v___y_1748_ = v_a_1740_;
v___y_1749_ = v_a_1741_;
v___y_1750_ = v_a_1742_;
v___y_1751_ = v_a_1743_;
v___y_1752_ = v_a_1744_;
v___y_1753_ = v_a_1745_;
goto v___jp_1747_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_type_1737_);
lean_dec_ref(v_e_1736_);
v_a_1817_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1797_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1797_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
v___jp_1747_:
{
if (v_report_1738_ == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref(v_type_1737_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_e_1736_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1755_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1736_);
v___x_1756_ = l_Lean_indentExpr(v_e_1736_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = l_Lean_indentExpr(v_type_1737_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1748_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1788_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1788_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1788_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint8_t v_verbose_1767_; 
v_verbose_1767_ = lean_ctor_get_uint8(v_a_1763_, 0);
lean_dec(v_a_1763_);
if (v_verbose_1767_ == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref_known(v___x_1761_, 2);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_e_1736_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_e_1736_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
lean_object* v___x_1771_; 
lean_del_object(v___x_1765_);
v___x_1771_ = l_Lean_Meta_Sym_reportIssue(v___x_1761_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1779_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v_e_1736_);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_e_1736_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_e_1736_);
v_a_1780_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1771_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref_known(v___x_1761_, 2);
lean_dec_ref(v_e_1736_);
v_a_1789_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1762_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1762_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1825_, uint8_t v_report_1826_, uint8_t v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; 
lean_inc(v_a_1833_);
lean_inc_ref(v_a_1832_);
lean_inc(v_a_1831_);
lean_inc_ref(v_a_1830_);
lean_inc_ref(v_e_1825_);
v___x_1835_ = lean_infer_type(v_e_1825_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_n(v_a_1836_, 2);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l_Lean_Meta_isProp(v_a_1836_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1850_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (v_a_1827_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_unbox(v_a_1838_);
lean_dec(v_a_1838_);
if (v___x_1846_ == 0)
{
lean_del_object(v___x_1840_);
goto v___jp_1842_;
}
else
{
lean_object* v___x_1848_; 
lean_dec(v_a_1836_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_e_1825_);
v___x_1848_ = v___x_1840_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_e_1825_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_del_object(v___x_1840_);
lean_dec(v_a_1838_);
goto v___jp_1842_;
}
v___jp_1842_:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1836_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1825_, v_a_1844_, v_report_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
return v___x_1845_;
}
else
{
lean_dec_ref(v_e_1825_);
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1836_);
lean_dec_ref(v_e_1825_);
v_a_1851_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1837_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1837_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_dec_ref(v_e_1825_);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1859_, uint8_t v_report_1860_, uint8_t v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
if (v_a_1861_ == 0)
{
lean_object* v___x_1869_; lean_object* v_canon_1870_; lean_object* v_cache_1871_; lean_object* v___x_1872_; 
v___x_1869_ = lean_st_ref_get(v_a_1863_);
v_canon_1870_ = lean_ctor_get(v___x_1869_, 10);
lean_inc_ref(v_canon_1870_);
lean_dec(v___x_1869_);
v_cache_1871_ = lean_ctor_get(v_canon_1870_, 0);
lean_inc_ref(v_cache_1871_);
lean_dec_ref(v_canon_1870_);
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1871_, v_e_1859_);
lean_dec_ref(v_cache_1871_);
if (lean_obj_tag(v___x_1872_) == 1)
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_e_1859_);
v_val_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v___x_1872_);
lean_inc_ref(v_e_1859_);
v___x_1881_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1859_, v_report_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1921_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1921_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1921_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v_canon_1887_; lean_object* v_share_1888_; lean_object* v_maxFVar_1889_; lean_object* v_proofInstInfo_1890_; lean_object* v_proofInstInfoFVar_1891_; lean_object* v_inferType_1892_; lean_object* v_getLevel_1893_; lean_object* v_congrInfo_1894_; lean_object* v_defEqI_1895_; lean_object* v_extensions_1896_; lean_object* v_issues_1897_; lean_object* v_instanceOverrides_1898_; uint8_t v_debug_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1920_; 
v___x_1886_ = lean_st_ref_take(v_a_1863_);
v_canon_1887_ = lean_ctor_get(v___x_1886_, 10);
v_share_1888_ = lean_ctor_get(v___x_1886_, 0);
v_maxFVar_1889_ = lean_ctor_get(v___x_1886_, 1);
v_proofInstInfo_1890_ = lean_ctor_get(v___x_1886_, 2);
v_proofInstInfoFVar_1891_ = lean_ctor_get(v___x_1886_, 3);
v_inferType_1892_ = lean_ctor_get(v___x_1886_, 4);
v_getLevel_1893_ = lean_ctor_get(v___x_1886_, 5);
v_congrInfo_1894_ = lean_ctor_get(v___x_1886_, 6);
v_defEqI_1895_ = lean_ctor_get(v___x_1886_, 7);
v_extensions_1896_ = lean_ctor_get(v___x_1886_, 8);
v_issues_1897_ = lean_ctor_get(v___x_1886_, 9);
v_instanceOverrides_1898_ = lean_ctor_get(v___x_1886_, 11);
v_debug_1899_ = lean_ctor_get_uint8(v___x_1886_, sizeof(void*)*12);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1901_ = v___x_1886_;
v_isShared_1902_ = v_isSharedCheck_1920_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_instanceOverrides_1898_);
lean_inc(v_canon_1887_);
lean_inc(v_issues_1897_);
lean_inc(v_extensions_1896_);
lean_inc(v_defEqI_1895_);
lean_inc(v_congrInfo_1894_);
lean_inc(v_getLevel_1893_);
lean_inc(v_inferType_1892_);
lean_inc(v_proofInstInfoFVar_1891_);
lean_inc(v_proofInstInfo_1890_);
lean_inc(v_maxFVar_1889_);
lean_inc(v_share_1888_);
lean_dec(v___x_1886_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1920_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_cache_1903_; lean_object* v_cacheInType_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1919_; 
v_cache_1903_ = lean_ctor_get(v_canon_1887_, 0);
v_cacheInType_1904_ = lean_ctor_get(v_canon_1887_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_canon_1887_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1906_ = v_canon_1887_;
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_cacheInType_1904_);
lean_inc(v_cache_1903_);
lean_dec(v_canon_1887_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_inc(v_a_1882_);
v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1903_, v_e_1859_, v_a_1882_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_cacheInType_1904_);
v___x_1910_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 10, v___x_1910_);
v___x_1912_ = v___x_1901_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_share_1888_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_maxFVar_1889_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_proofInstInfo_1890_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v_proofInstInfoFVar_1891_);
lean_ctor_set(v_reuseFailAlloc_1917_, 4, v_inferType_1892_);
lean_ctor_set(v_reuseFailAlloc_1917_, 5, v_getLevel_1893_);
lean_ctor_set(v_reuseFailAlloc_1917_, 6, v_congrInfo_1894_);
lean_ctor_set(v_reuseFailAlloc_1917_, 7, v_defEqI_1895_);
lean_ctor_set(v_reuseFailAlloc_1917_, 8, v_extensions_1896_);
lean_ctor_set(v_reuseFailAlloc_1917_, 9, v_issues_1897_);
lean_ctor_set(v_reuseFailAlloc_1917_, 10, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1917_, 11, v_instanceOverrides_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1917_, sizeof(void*)*12, v_debug_1899_);
v___x_1912_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_st_ref_put(v_a_1863_, v___x_1912_);
if (v_isShared_1885_ == 0)
{
v___x_1915_ = v___x_1884_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1882_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1859_);
return v___x_1881_;
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v_canon_1923_; lean_object* v_cacheInType_1924_; lean_object* v___x_1925_; 
v___x_1922_ = lean_st_ref_get(v_a_1863_);
v_canon_1923_ = lean_ctor_get(v___x_1922_, 10);
lean_inc_ref(v_canon_1923_);
lean_dec(v___x_1922_);
v_cacheInType_1924_ = lean_ctor_get(v_canon_1923_, 1);
lean_inc_ref(v_cacheInType_1924_);
lean_dec_ref(v_canon_1923_);
v___x_1925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1924_, v_e_1859_);
lean_dec_ref(v_cacheInType_1924_);
if (lean_obj_tag(v___x_1925_) == 1)
{
lean_object* v_val_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_e_1859_);
v_val_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_val_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 0);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_val_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v___x_1934_; 
lean_dec(v___x_1925_);
lean_inc_ref(v_e_1859_);
v___x_1934_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1859_, v_report_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1974_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1974_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1974_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v_canon_1940_; lean_object* v_share_1941_; lean_object* v_maxFVar_1942_; lean_object* v_proofInstInfo_1943_; lean_object* v_proofInstInfoFVar_1944_; lean_object* v_inferType_1945_; lean_object* v_getLevel_1946_; lean_object* v_congrInfo_1947_; lean_object* v_defEqI_1948_; lean_object* v_extensions_1949_; lean_object* v_issues_1950_; lean_object* v_instanceOverrides_1951_; uint8_t v_debug_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1973_; 
v___x_1939_ = lean_st_ref_take(v_a_1863_);
v_canon_1940_ = lean_ctor_get(v___x_1939_, 10);
v_share_1941_ = lean_ctor_get(v___x_1939_, 0);
v_maxFVar_1942_ = lean_ctor_get(v___x_1939_, 1);
v_proofInstInfo_1943_ = lean_ctor_get(v___x_1939_, 2);
v_proofInstInfoFVar_1944_ = lean_ctor_get(v___x_1939_, 3);
v_inferType_1945_ = lean_ctor_get(v___x_1939_, 4);
v_getLevel_1946_ = lean_ctor_get(v___x_1939_, 5);
v_congrInfo_1947_ = lean_ctor_get(v___x_1939_, 6);
v_defEqI_1948_ = lean_ctor_get(v___x_1939_, 7);
v_extensions_1949_ = lean_ctor_get(v___x_1939_, 8);
v_issues_1950_ = lean_ctor_get(v___x_1939_, 9);
v_instanceOverrides_1951_ = lean_ctor_get(v___x_1939_, 11);
v_debug_1952_ = lean_ctor_get_uint8(v___x_1939_, sizeof(void*)*12);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1954_ = v___x_1939_;
v_isShared_1955_ = v_isSharedCheck_1973_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_instanceOverrides_1951_);
lean_inc(v_canon_1940_);
lean_inc(v_issues_1950_);
lean_inc(v_extensions_1949_);
lean_inc(v_defEqI_1948_);
lean_inc(v_congrInfo_1947_);
lean_inc(v_getLevel_1946_);
lean_inc(v_inferType_1945_);
lean_inc(v_proofInstInfoFVar_1944_);
lean_inc(v_proofInstInfo_1943_);
lean_inc(v_maxFVar_1942_);
lean_inc(v_share_1941_);
lean_dec(v___x_1939_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1973_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_cache_1956_; lean_object* v_cacheInType_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1972_; 
v_cache_1956_ = lean_ctor_get(v_canon_1940_, 0);
v_cacheInType_1957_ = lean_ctor_get(v_canon_1940_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_canon_1940_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1959_ = v_canon_1940_;
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_cacheInType_1957_);
lean_inc(v_cache_1956_);
lean_dec(v_canon_1940_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc(v_a_1935_);
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1957_, v_e_1859_, v_a_1935_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_cache_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 10, v___x_1963_);
v___x_1965_ = v___x_1954_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_share_1941_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_maxFVar_1942_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_proofInstInfo_1943_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_proofInstInfoFVar_1944_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_inferType_1945_);
lean_ctor_set(v_reuseFailAlloc_1970_, 5, v_getLevel_1946_);
lean_ctor_set(v_reuseFailAlloc_1970_, 6, v_congrInfo_1947_);
lean_ctor_set(v_reuseFailAlloc_1970_, 7, v_defEqI_1948_);
lean_ctor_set(v_reuseFailAlloc_1970_, 8, v_extensions_1949_);
lean_ctor_set(v_reuseFailAlloc_1970_, 9, v_issues_1950_);
lean_ctor_set(v_reuseFailAlloc_1970_, 10, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 11, v_instanceOverrides_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1970_, sizeof(void*)*12, v_debug_1952_);
v___x_1965_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_st_ref_put(v_a_1863_, v___x_1965_);
if (v_isShared_1938_ == 0)
{
v___x_1968_ = v___x_1937_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1935_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1859_);
return v___x_1934_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1991_ = l_Lean_mkConst(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1992_, lean_object* v_prop_1993_, lean_object* v_inst_1994_, lean_object* v_e_1995_, uint8_t v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
lean_inc_ref(v_prop_1993_);
v___x_2004_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1993_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2047_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2047_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2047_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___y_2010_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_2005_);
v___x_2016_ = l_Lean_Expr_app___override(v___x_2015_, v_a_2005_);
if (v_a_1996_ == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2016_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___y_2020_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
if (lean_obj_tag(v_a_2018_) == 0)
{
lean_inc_ref(v_inst_1994_);
v___y_2020_ = v_inst_1994_;
goto v___jp_2019_;
}
else
{
lean_object* v_val_2036_; 
v_val_2036_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v_a_2018_, 1);
v___y_2020_ = v_val_2036_;
goto v___jp_2019_;
}
v___jp_2019_:
{
lean_object* v___x_2021_; 
lean_inc_ref(v_inst_1994_);
v___x_2021_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1994_, v___y_2020_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2035_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2035_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2035_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
size_t v___x_2026_; size_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2026_ = lean_ptr_addr(v_prop_1993_);
lean_dec_ref(v_prop_1993_);
v___x_2027_ = lean_ptr_addr(v_a_2005_);
v___x_2028_ = lean_usize_dec_eq(v___x_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_del_object(v___x_2024_);
lean_dec_ref(v_e_1995_);
lean_dec_ref(v_inst_1994_);
v___y_2010_ = v_a_2022_;
goto v___jp_2009_;
}
else
{
size_t v___x_2029_; size_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_ptr_addr(v_inst_1994_);
lean_dec_ref(v_inst_1994_);
v___x_2030_ = lean_ptr_addr(v_a_2022_);
v___x_2031_ = lean_usize_dec_eq(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_del_object(v___x_2024_);
lean_dec_ref(v_e_1995_);
v___y_2010_ = v_a_2022_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_a_2022_);
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
lean_dec_ref(v_g_1992_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v_e_1995_);
v___x_2033_ = v___x_2024_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_e_1995_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
lean_dec_ref(v_e_1995_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_prop_1993_);
lean_dec_ref(v_g_1992_);
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
lean_dec_ref(v_e_1995_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_prop_1993_);
lean_dec_ref(v_g_1992_);
v_a_2037_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2017_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2017_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
uint8_t v___x_2045_; lean_object* v___x_2046_; 
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
lean_dec_ref(v_e_1995_);
lean_dec_ref(v_prop_1993_);
lean_dec_ref(v_g_1992_);
v___x_2045_ = 0;
v___x_2046_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_inst_1994_, v___x_2016_, v___x_2045_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v___x_2046_;
}
v___jp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = l_Lean_mkAppB(v_g_1992_, v_a_2005_, v___y_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec_ref(v_e_1995_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_prop_1993_);
lean_dec_ref(v_g_1992_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2048_, lean_object* v_prop_2049_, lean_object* v_h_2050_, lean_object* v_e_2051_, uint8_t v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
if (v_a_2052_ == 0)
{
lean_object* v___x_2060_; lean_object* v_canon_2061_; lean_object* v_cache_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_st_ref_get(v_a_2054_);
v_canon_2061_ = lean_ctor_get(v___x_2060_, 10);
lean_inc_ref(v_canon_2061_);
lean_dec(v___x_2060_);
v_cache_2062_ = lean_ctor_get(v_canon_2061_, 0);
lean_inc_ref(v_cache_2062_);
lean_dec_ref(v_canon_2061_);
v___x_2063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2062_, v_e_2051_);
lean_dec_ref(v_cache_2062_);
if (lean_obj_tag(v___x_2063_) == 1)
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_e_2051_);
lean_dec_ref(v_h_2050_);
lean_dec_ref(v_prop_2049_);
lean_dec_ref(v_g_2048_);
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v___x_2072_; 
lean_dec(v___x_2063_);
lean_inc_ref(v_e_2051_);
v___x_2072_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2048_, v_prop_2049_, v_h_2050_, v_e_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2112_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2112_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2112_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v_canon_2078_; lean_object* v_share_2079_; lean_object* v_maxFVar_2080_; lean_object* v_proofInstInfo_2081_; lean_object* v_proofInstInfoFVar_2082_; lean_object* v_inferType_2083_; lean_object* v_getLevel_2084_; lean_object* v_congrInfo_2085_; lean_object* v_defEqI_2086_; lean_object* v_extensions_2087_; lean_object* v_issues_2088_; lean_object* v_instanceOverrides_2089_; uint8_t v_debug_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2111_; 
v___x_2077_ = lean_st_ref_take(v_a_2054_);
v_canon_2078_ = lean_ctor_get(v___x_2077_, 10);
v_share_2079_ = lean_ctor_get(v___x_2077_, 0);
v_maxFVar_2080_ = lean_ctor_get(v___x_2077_, 1);
v_proofInstInfo_2081_ = lean_ctor_get(v___x_2077_, 2);
v_proofInstInfoFVar_2082_ = lean_ctor_get(v___x_2077_, 3);
v_inferType_2083_ = lean_ctor_get(v___x_2077_, 4);
v_getLevel_2084_ = lean_ctor_get(v___x_2077_, 5);
v_congrInfo_2085_ = lean_ctor_get(v___x_2077_, 6);
v_defEqI_2086_ = lean_ctor_get(v___x_2077_, 7);
v_extensions_2087_ = lean_ctor_get(v___x_2077_, 8);
v_issues_2088_ = lean_ctor_get(v___x_2077_, 9);
v_instanceOverrides_2089_ = lean_ctor_get(v___x_2077_, 11);
v_debug_2090_ = lean_ctor_get_uint8(v___x_2077_, sizeof(void*)*12);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2092_ = v___x_2077_;
v_isShared_2093_ = v_isSharedCheck_2111_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_instanceOverrides_2089_);
lean_inc(v_canon_2078_);
lean_inc(v_issues_2088_);
lean_inc(v_extensions_2087_);
lean_inc(v_defEqI_2086_);
lean_inc(v_congrInfo_2085_);
lean_inc(v_getLevel_2084_);
lean_inc(v_inferType_2083_);
lean_inc(v_proofInstInfoFVar_2082_);
lean_inc(v_proofInstInfo_2081_);
lean_inc(v_maxFVar_2080_);
lean_inc(v_share_2079_);
lean_dec(v___x_2077_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2111_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_cache_2094_; lean_object* v_cacheInType_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2110_; 
v_cache_2094_ = lean_ctor_get(v_canon_2078_, 0);
v_cacheInType_2095_ = lean_ctor_get(v_canon_2078_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_canon_2078_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2097_ = v_canon_2078_;
v_isShared_2098_ = v_isSharedCheck_2110_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_cacheInType_2095_);
lean_inc(v_cache_2094_);
lean_dec(v_canon_2078_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2110_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_inc(v_a_2073_);
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2094_, v_e_2051_, v_a_2073_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_cacheInType_2095_);
v___x_2101_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 10, v___x_2101_);
v___x_2103_ = v___x_2092_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_share_2079_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_maxFVar_2080_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_proofInstInfo_2081_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_proofInstInfoFVar_2082_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_inferType_2083_);
lean_ctor_set(v_reuseFailAlloc_2108_, 5, v_getLevel_2084_);
lean_ctor_set(v_reuseFailAlloc_2108_, 6, v_congrInfo_2085_);
lean_ctor_set(v_reuseFailAlloc_2108_, 7, v_defEqI_2086_);
lean_ctor_set(v_reuseFailAlloc_2108_, 8, v_extensions_2087_);
lean_ctor_set(v_reuseFailAlloc_2108_, 9, v_issues_2088_);
lean_ctor_set(v_reuseFailAlloc_2108_, 10, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2108_, 11, v_instanceOverrides_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*12, v_debug_2090_);
v___x_2103_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_st_ref_put(v_a_2054_, v___x_2103_);
if (v_isShared_2076_ == 0)
{
v___x_2106_ = v___x_2075_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2073_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2051_);
return v___x_2072_;
}
}
}
else
{
lean_object* v___x_2113_; lean_object* v_canon_2114_; lean_object* v_cacheInType_2115_; lean_object* v___x_2116_; 
v___x_2113_ = lean_st_ref_get(v_a_2054_);
v_canon_2114_ = lean_ctor_get(v___x_2113_, 10);
lean_inc_ref(v_canon_2114_);
lean_dec(v___x_2113_);
v_cacheInType_2115_ = lean_ctor_get(v_canon_2114_, 1);
lean_inc_ref(v_cacheInType_2115_);
lean_dec_ref(v_canon_2114_);
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2115_, v_e_2051_);
lean_dec_ref(v_cacheInType_2115_);
if (lean_obj_tag(v___x_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_e_2051_);
lean_dec_ref(v_h_2050_);
lean_dec_ref(v_prop_2049_);
lean_dec_ref(v_g_2048_);
v_val_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_val_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 0);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_val_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
lean_object* v___x_2125_; 
lean_dec(v___x_2116_);
lean_inc_ref(v_e_2051_);
v___x_2125_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2048_, v_prop_2049_, v_h_2050_, v_e_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2165_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2165_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2165_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v_canon_2131_; lean_object* v_share_2132_; lean_object* v_maxFVar_2133_; lean_object* v_proofInstInfo_2134_; lean_object* v_proofInstInfoFVar_2135_; lean_object* v_inferType_2136_; lean_object* v_getLevel_2137_; lean_object* v_congrInfo_2138_; lean_object* v_defEqI_2139_; lean_object* v_extensions_2140_; lean_object* v_issues_2141_; lean_object* v_instanceOverrides_2142_; uint8_t v_debug_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2164_; 
v___x_2130_ = lean_st_ref_take(v_a_2054_);
v_canon_2131_ = lean_ctor_get(v___x_2130_, 10);
v_share_2132_ = lean_ctor_get(v___x_2130_, 0);
v_maxFVar_2133_ = lean_ctor_get(v___x_2130_, 1);
v_proofInstInfo_2134_ = lean_ctor_get(v___x_2130_, 2);
v_proofInstInfoFVar_2135_ = lean_ctor_get(v___x_2130_, 3);
v_inferType_2136_ = lean_ctor_get(v___x_2130_, 4);
v_getLevel_2137_ = lean_ctor_get(v___x_2130_, 5);
v_congrInfo_2138_ = lean_ctor_get(v___x_2130_, 6);
v_defEqI_2139_ = lean_ctor_get(v___x_2130_, 7);
v_extensions_2140_ = lean_ctor_get(v___x_2130_, 8);
v_issues_2141_ = lean_ctor_get(v___x_2130_, 9);
v_instanceOverrides_2142_ = lean_ctor_get(v___x_2130_, 11);
v_debug_2143_ = lean_ctor_get_uint8(v___x_2130_, sizeof(void*)*12);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2145_ = v___x_2130_;
v_isShared_2146_ = v_isSharedCheck_2164_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_instanceOverrides_2142_);
lean_inc(v_canon_2131_);
lean_inc(v_issues_2141_);
lean_inc(v_extensions_2140_);
lean_inc(v_defEqI_2139_);
lean_inc(v_congrInfo_2138_);
lean_inc(v_getLevel_2137_);
lean_inc(v_inferType_2136_);
lean_inc(v_proofInstInfoFVar_2135_);
lean_inc(v_proofInstInfo_2134_);
lean_inc(v_maxFVar_2133_);
lean_inc(v_share_2132_);
lean_dec(v___x_2130_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2164_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_cache_2147_; lean_object* v_cacheInType_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2163_; 
v_cache_2147_ = lean_ctor_get(v_canon_2131_, 0);
v_cacheInType_2148_ = lean_ctor_get(v_canon_2131_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_canon_2131_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2150_ = v_canon_2131_;
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_cacheInType_2148_);
lean_inc(v_cache_2147_);
lean_dec(v_canon_2131_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_inc(v_a_2126_);
v___x_2152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2148_, v_e_2051_, v_a_2126_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_cache_2147_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 10, v___x_2154_);
v___x_2156_ = v___x_2145_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_share_2132_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_maxFVar_2133_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_proofInstInfo_2134_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_proofInstInfoFVar_2135_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_inferType_2136_);
lean_ctor_set(v_reuseFailAlloc_2161_, 5, v_getLevel_2137_);
lean_ctor_set(v_reuseFailAlloc_2161_, 6, v_congrInfo_2138_);
lean_ctor_set(v_reuseFailAlloc_2161_, 7, v_defEqI_2139_);
lean_ctor_set(v_reuseFailAlloc_2161_, 8, v_extensions_2140_);
lean_ctor_set(v_reuseFailAlloc_2161_, 9, v_issues_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 10, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2161_, 11, v_instanceOverrides_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*12, v_debug_2143_);
v___x_2156_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_st_ref_put(v_a_2054_, v___x_2156_);
if (v_isShared_2129_ == 0)
{
v___x_2159_ = v___x_2128_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2126_);
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
}
else
{
lean_dec_ref(v_e_2051_);
return v___x_2125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2166_, lean_object* v_prop_2167_, lean_object* v_h_2168_, lean_object* v_e_2169_, uint8_t v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_a_2179_; 
if (v_a_2170_ == 0)
{
lean_object* v___x_2213_; lean_object* v_canon_2214_; lean_object* v_cache_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_st_ref_get(v_a_2172_);
v_canon_2214_ = lean_ctor_get(v___x_2213_, 10);
lean_inc_ref(v_canon_2214_);
lean_dec(v___x_2213_);
v_cache_2215_ = lean_ctor_get(v_canon_2214_, 0);
lean_inc_ref(v_cache_2215_);
lean_dec_ref(v_canon_2214_);
v___x_2216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2215_, v_e_2169_);
lean_dec_ref(v_cache_2215_);
if (lean_obj_tag(v___x_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_e_2169_);
lean_dec_ref(v_h_2168_);
lean_dec_ref(v_prop_2167_);
lean_dec_ref(v_g_2166_);
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_val_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 0);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_val_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
else
{
lean_object* v___x_2225_; 
lean_dec(v___x_2216_);
lean_inc_ref(v_prop_2167_);
v___x_2225_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2167_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc_n(v_a_2226_, 2);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2226_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___y_2230_; lean_object* v___y_2233_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
if (lean_obj_tag(v_a_2228_) == 0)
{
lean_inc_ref(v_h_2168_);
v___y_2233_ = v_h_2168_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2240_; 
v_val_2240_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v_a_2228_, 1);
v___y_2233_ = v_val_2240_;
goto v___jp_2232_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_mkAppB(v_g_2166_, v_a_2226_, v___y_2230_);
v_a_2179_ = v___x_2231_;
goto v___jp_2178_;
}
v___jp_2232_:
{
size_t v___x_2234_; size_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2234_ = lean_ptr_addr(v_prop_2167_);
lean_dec_ref(v_prop_2167_);
v___x_2235_ = lean_ptr_addr(v_a_2226_);
v___x_2236_ = lean_usize_dec_eq(v___x_2234_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_dec_ref(v_h_2168_);
v___y_2230_ = v___y_2233_;
goto v___jp_2229_;
}
else
{
size_t v___x_2237_; size_t v___x_2238_; uint8_t v___x_2239_; 
v___x_2237_ = lean_ptr_addr(v_h_2168_);
lean_dec_ref(v_h_2168_);
v___x_2238_ = lean_ptr_addr(v___y_2233_);
v___x_2239_ = lean_usize_dec_eq(v___x_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
v___y_2230_ = v___y_2233_;
goto v___jp_2229_;
}
else
{
lean_dec_ref(v___y_2233_);
lean_dec(v_a_2226_);
lean_dec_ref(v_g_2166_);
lean_inc_ref(v_e_2169_);
v_a_2179_ = v_e_2169_;
goto v___jp_2178_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_a_2226_);
lean_dec_ref(v_e_2169_);
lean_dec_ref(v_h_2168_);
lean_dec_ref(v_prop_2167_);
lean_dec_ref(v_g_2166_);
v_a_2241_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2227_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2227_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_dec_ref(v_e_2169_);
lean_dec_ref(v_h_2168_);
lean_dec_ref(v_prop_2167_);
lean_dec_ref(v_g_2166_);
return v___x_2225_;
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v_canon_2250_; lean_object* v_cacheInType_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v_g_2166_);
v___x_2249_ = lean_st_ref_get(v_a_2172_);
v_canon_2250_ = lean_ctor_get(v___x_2249_, 10);
lean_inc_ref(v_canon_2250_);
lean_dec(v___x_2249_);
v_cacheInType_2251_ = lean_ctor_get(v_canon_2250_, 1);
lean_inc_ref(v_cacheInType_2251_);
lean_dec_ref(v_canon_2250_);
v___x_2252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2251_, v_e_2169_);
lean_dec_ref(v_cacheInType_2251_);
if (lean_obj_tag(v___x_2252_) == 1)
{
lean_object* v_val_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v_e_2169_);
lean_dec_ref(v_h_2168_);
lean_dec_ref(v_prop_2167_);
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_val_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 0);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_val_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v___x_2261_; 
lean_dec(v___x_2252_);
v___x_2261_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2167_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = 0;
v___x_2264_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_h_2168_, v_a_2262_, v___x_2263_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2304_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2304_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2304_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v_canon_2270_; lean_object* v_share_2271_; lean_object* v_maxFVar_2272_; lean_object* v_proofInstInfo_2273_; lean_object* v_proofInstInfoFVar_2274_; lean_object* v_inferType_2275_; lean_object* v_getLevel_2276_; lean_object* v_congrInfo_2277_; lean_object* v_defEqI_2278_; lean_object* v_extensions_2279_; lean_object* v_issues_2280_; lean_object* v_instanceOverrides_2281_; uint8_t v_debug_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2303_; 
v___x_2269_ = lean_st_ref_take(v_a_2172_);
v_canon_2270_ = lean_ctor_get(v___x_2269_, 10);
v_share_2271_ = lean_ctor_get(v___x_2269_, 0);
v_maxFVar_2272_ = lean_ctor_get(v___x_2269_, 1);
v_proofInstInfo_2273_ = lean_ctor_get(v___x_2269_, 2);
v_proofInstInfoFVar_2274_ = lean_ctor_get(v___x_2269_, 3);
v_inferType_2275_ = lean_ctor_get(v___x_2269_, 4);
v_getLevel_2276_ = lean_ctor_get(v___x_2269_, 5);
v_congrInfo_2277_ = lean_ctor_get(v___x_2269_, 6);
v_defEqI_2278_ = lean_ctor_get(v___x_2269_, 7);
v_extensions_2279_ = lean_ctor_get(v___x_2269_, 8);
v_issues_2280_ = lean_ctor_get(v___x_2269_, 9);
v_instanceOverrides_2281_ = lean_ctor_get(v___x_2269_, 11);
v_debug_2282_ = lean_ctor_get_uint8(v___x_2269_, sizeof(void*)*12);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2284_ = v___x_2269_;
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_instanceOverrides_2281_);
lean_inc(v_canon_2270_);
lean_inc(v_issues_2280_);
lean_inc(v_extensions_2279_);
lean_inc(v_defEqI_2278_);
lean_inc(v_congrInfo_2277_);
lean_inc(v_getLevel_2276_);
lean_inc(v_inferType_2275_);
lean_inc(v_proofInstInfoFVar_2274_);
lean_inc(v_proofInstInfo_2273_);
lean_inc(v_maxFVar_2272_);
lean_inc(v_share_2271_);
lean_dec(v___x_2269_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_cache_2286_; lean_object* v_cacheInType_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2302_; 
v_cache_2286_ = lean_ctor_get(v_canon_2270_, 0);
v_cacheInType_2287_ = lean_ctor_get(v_canon_2270_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_canon_2270_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2289_ = v_canon_2270_;
v_isShared_2290_ = v_isSharedCheck_2302_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_cacheInType_2287_);
lean_inc(v_cache_2286_);
lean_dec(v_canon_2270_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2302_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
lean_inc(v_a_2265_);
v___x_2291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2287_, v_e_2169_, v_a_2265_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_cache_2286_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2295_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 10, v___x_2293_);
v___x_2295_ = v___x_2284_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_share_2271_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_maxFVar_2272_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_proofInstInfo_2273_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_proofInstInfoFVar_2274_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_inferType_2275_);
lean_ctor_set(v_reuseFailAlloc_2300_, 5, v_getLevel_2276_);
lean_ctor_set(v_reuseFailAlloc_2300_, 6, v_congrInfo_2277_);
lean_ctor_set(v_reuseFailAlloc_2300_, 7, v_defEqI_2278_);
lean_ctor_set(v_reuseFailAlloc_2300_, 8, v_extensions_2279_);
lean_ctor_set(v_reuseFailAlloc_2300_, 9, v_issues_2280_);
lean_ctor_set(v_reuseFailAlloc_2300_, 10, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2300_, 11, v_instanceOverrides_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2300_, sizeof(void*)*12, v_debug_2282_);
v___x_2295_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_st_ref_put(v_a_2172_, v___x_2295_);
if (v_isShared_2268_ == 0)
{
v___x_2298_ = v___x_2267_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2265_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2169_);
return v___x_2264_;
}
}
else
{
lean_dec_ref(v_e_2169_);
lean_dec_ref(v_h_2168_);
return v___x_2261_;
}
}
}
v___jp_2178_:
{
lean_object* v___x_2180_; lean_object* v_canon_2181_; lean_object* v_share_2182_; lean_object* v_maxFVar_2183_; lean_object* v_proofInstInfo_2184_; lean_object* v_proofInstInfoFVar_2185_; lean_object* v_inferType_2186_; lean_object* v_getLevel_2187_; lean_object* v_congrInfo_2188_; lean_object* v_defEqI_2189_; lean_object* v_extensions_2190_; lean_object* v_issues_2191_; lean_object* v_instanceOverrides_2192_; uint8_t v_debug_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2212_; 
v___x_2180_ = lean_st_ref_take(v_a_2172_);
v_canon_2181_ = lean_ctor_get(v___x_2180_, 10);
v_share_2182_ = lean_ctor_get(v___x_2180_, 0);
v_maxFVar_2183_ = lean_ctor_get(v___x_2180_, 1);
v_proofInstInfo_2184_ = lean_ctor_get(v___x_2180_, 2);
v_proofInstInfoFVar_2185_ = lean_ctor_get(v___x_2180_, 3);
v_inferType_2186_ = lean_ctor_get(v___x_2180_, 4);
v_getLevel_2187_ = lean_ctor_get(v___x_2180_, 5);
v_congrInfo_2188_ = lean_ctor_get(v___x_2180_, 6);
v_defEqI_2189_ = lean_ctor_get(v___x_2180_, 7);
v_extensions_2190_ = lean_ctor_get(v___x_2180_, 8);
v_issues_2191_ = lean_ctor_get(v___x_2180_, 9);
v_instanceOverrides_2192_ = lean_ctor_get(v___x_2180_, 11);
v_debug_2193_ = lean_ctor_get_uint8(v___x_2180_, sizeof(void*)*12);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2195_ = v___x_2180_;
v_isShared_2196_ = v_isSharedCheck_2212_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_instanceOverrides_2192_);
lean_inc(v_canon_2181_);
lean_inc(v_issues_2191_);
lean_inc(v_extensions_2190_);
lean_inc(v_defEqI_2189_);
lean_inc(v_congrInfo_2188_);
lean_inc(v_getLevel_2187_);
lean_inc(v_inferType_2186_);
lean_inc(v_proofInstInfoFVar_2185_);
lean_inc(v_proofInstInfo_2184_);
lean_inc(v_maxFVar_2183_);
lean_inc(v_share_2182_);
lean_dec(v___x_2180_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2212_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_cache_2197_; lean_object* v_cacheInType_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2211_; 
v_cache_2197_ = lean_ctor_get(v_canon_2181_, 0);
v_cacheInType_2198_ = lean_ctor_get(v_canon_2181_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_canon_2181_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2200_ = v_canon_2181_;
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_cacheInType_2198_);
lean_inc(v_cache_2197_);
lean_dec(v_canon_2181_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
lean_inc_ref(v_a_2179_);
v___x_2202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2197_, v_e_2169_, v_a_2179_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_cacheInType_2198_);
v___x_2204_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 10, v___x_2204_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_share_2182_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_maxFVar_2183_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_proofInstInfo_2184_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_proofInstInfoFVar_2185_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_inferType_2186_);
lean_ctor_set(v_reuseFailAlloc_2209_, 5, v_getLevel_2187_);
lean_ctor_set(v_reuseFailAlloc_2209_, 6, v_congrInfo_2188_);
lean_ctor_set(v_reuseFailAlloc_2209_, 7, v_defEqI_2189_);
lean_ctor_set(v_reuseFailAlloc_2209_, 8, v_extensions_2190_);
lean_ctor_set(v_reuseFailAlloc_2209_, 9, v_issues_2191_);
lean_ctor_set(v_reuseFailAlloc_2209_, 10, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2209_, 11, v_instanceOverrides_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2209_, sizeof(void*)*12, v_debug_2193_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_st_ref_put(v_a_2172_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2179_);
return v___x_2208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2305_, lean_object* v_snd_2306_, lean_object* v_a_2307_, uint8_t v___x_2308_, lean_object* v_fst_2309_, lean_object* v___x_2310_, lean_object* v_____r_2311_, uint8_t v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_arg_x27_2321_; lean_object* v___x_2355_; 
lean_inc_ref(v___x_2305_);
v___x_2355_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2310_, v_a_2307_, v___x_2305_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; uint8_t v___x_2357_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = lean_unbox(v_a_2356_);
lean_dec(v_a_2356_);
switch(v___x_2357_)
{
case 0:
{
lean_object* v___x_2358_; 
lean_inc_ref(v___x_2305_);
v___x_2358_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2305_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v_arg_x27_2321_ = v_a_2359_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2360_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2358_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2358_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
case 1:
{
lean_object* v___x_2368_; 
lean_inc_ref(v___x_2305_);
v___x_2368_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2305_, v___y_2316_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = l_Lean_Expr_cleanupAnnotations(v_a_2369_);
v___x_2371_ = l_Lean_Expr_isApp(v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec_ref(v___x_2370_);
goto v___jp_2344_;
}
else
{
lean_object* v_arg_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_arg_2372_ = lean_ctor_get(v___x_2370_, 1);
lean_inc_ref(v_arg_2372_);
v___x_2373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2370_);
v___x_2374_ = l_Lean_Expr_isApp(v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec_ref(v___x_2373_);
lean_dec_ref(v_arg_2372_);
goto v___jp_2344_;
}
else
{
lean_object* v_arg_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_arg_2375_ = lean_ctor_get(v___x_2373_, 1);
lean_inc_ref(v_arg_2375_);
v___x_2376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2373_);
v___x_2377_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2378_ = l_Lean_Expr_isConstOf(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2380_ = l_Lean_Expr_isConstOf(v___x_2376_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref(v___x_2376_);
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
goto v___jp_2344_;
}
else
{
lean_object* v___x_2381_; 
lean_inc_ref(v___x_2305_);
v___x_2381_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2376_, v_arg_2375_, v_arg_2372_, v___x_2305_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v_arg_x27_2321_ = v_a_2382_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2383_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2381_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2381_);
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
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_2391_; 
lean_inc_ref(v___x_2305_);
v___x_2391_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2376_, v_arg_2375_, v_arg_2372_, v___x_2305_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_arg_x27_2321_ = v_a_2392_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2393_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2401_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2368_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2368_);
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
default: 
{
goto v___jp_2333_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2409_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2355_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2355_);
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
v___jp_2320_:
{
size_t v___x_2322_; size_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = lean_ptr_addr(v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2323_ = lean_ptr_addr(v_arg_x27_2321_);
v___x_2324_ = lean_usize_dec_eq(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_fst_2309_);
v___x_2325_ = lean_array_fset(v_snd_2306_, v_a_2307_, v_arg_x27_2321_);
v___x_2326_ = lean_box(v___x_2308_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec_ref(v_arg_x27_2321_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_fst_2309_);
lean_ctor_set(v___x_2330_, 1, v_snd_2306_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
v___jp_2333_:
{
lean_object* v___x_2334_; 
lean_inc_ref(v___x_2305_);
v___x_2334_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2305_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v_arg_x27_2321_ = v_a_2335_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2336_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2334_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2334_);
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
v___jp_2344_:
{
lean_object* v___x_2345_; 
lean_inc_ref(v___x_2305_);
v___x_2345_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2305_, v___x_2308_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_arg_x27_2321_ = v_a_2346_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_fst_2309_);
lean_dec(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_a_2347_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2345_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2345_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2422_ = l_Lean_Name_append(v___x_2421_, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2428_ = l_Lean_stringToMessageData(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2432_, lean_object* v___x_2433_, lean_object* v_a_2434_, lean_object* v_b_2435_, uint8_t v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___y_2445_; uint8_t v___x_2467_; 
v___x_2467_ = lean_nat_dec_lt(v_a_2434_, v_upperBound_2432_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec(v_a_2434_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_b_2435_);
return v___x_2468_;
}
else
{
lean_object* v_toCold_2469_; lean_object* v_options_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2536_; 
v_toCold_2469_ = lean_ctor_get(v___y_2441_, 0);
v_options_2470_ = lean_ctor_get(v_toCold_2469_, 2);
v_fst_2471_ = lean_ctor_get(v_b_2435_, 0);
v_snd_2472_ = lean_ctor_get(v_b_2435_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_b_2435_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2474_ = v_b_2435_;
v_isShared_2475_ = v_isSharedCheck_2536_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_snd_2472_);
lean_inc(v_fst_2471_);
lean_dec(v_b_2435_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2536_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_inheritedTraceOptions_2476_; uint8_t v_hasTrace_2477_; lean_object* v___x_2478_; 
v_inheritedTraceOptions_2476_ = lean_ctor_get(v_toCold_2469_, 11);
v_hasTrace_2477_ = lean_ctor_get_uint8(v_options_2470_, sizeof(void*)*1);
v___x_2478_ = lean_array_fget(v_snd_2472_, v_a_2434_);
if (v_hasTrace_2477_ == 0)
{
lean_del_object(v___x_2474_);
goto v___jp_2479_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2483_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2476_, v_options_2470_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_del_object(v___x_2474_);
goto v___jp_2479_;
}
else
{
lean_object* v___x_2485_; 
lean_inc(v___x_2478_);
v___x_2485_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2433_, v_a_2434_, v___x_2478_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___x_2478_);
v___x_2487_ = lean_infer_type(v___x_2478_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___y_2491_; uint8_t v___x_2515_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2515_ = lean_unbox(v_a_2486_);
lean_dec(v_a_2486_);
switch(v___x_2515_)
{
case 0:
{
lean_object* v___x_2516_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2491_ = v___x_2516_;
goto v___jp_2490_;
}
case 1:
{
lean_object* v___x_2517_; 
v___x_2517_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2491_ = v___x_2517_;
goto v___jp_2490_;
}
case 2:
{
lean_object* v___x_2518_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2491_ = v___x_2518_;
goto v___jp_2490_;
}
default: 
{
lean_object* v___x_2519_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2491_ = v___x_2519_;
goto v___jp_2490_;
}
}
v___jp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_inc(v___y_2491_);
v___x_2492_ = l_Lean_MessageData_ofFormat(v___y_2491_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 7);
lean_ctor_set(v___x_2474_, 1, v___x_2492_);
lean_ctor_set(v___x_2474_, 0, v___x_2489_);
v___x_2494_ = v___x_2474_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2495_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
lean_inc(v___x_2478_);
v___x_2497_ = l_Lean_MessageData_ofExpr(v___x_2478_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = l_Lean_MessageData_ofExpr(v_a_2488_);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2482_, v___x_2502_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2478_, v_snd_2472_, v_a_2434_, v___x_2467_, v_fst_2471_, v___x_2433_, v_a_2504_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
v___y_2445_ = v___x_2505_;
goto v___jp_2444_;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v___x_2478_);
lean_dec(v_snd_2472_);
lean_dec(v_fst_2471_);
lean_dec(v_a_2434_);
v_a_2506_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2503_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2503_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2486_);
lean_dec(v___x_2478_);
lean_del_object(v___x_2474_);
lean_dec(v_snd_2472_);
lean_dec(v_fst_2471_);
lean_dec(v_a_2434_);
v_a_2520_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2487_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2487_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___x_2478_);
lean_del_object(v___x_2474_);
lean_dec(v_snd_2472_);
lean_dec(v_fst_2471_);
lean_dec(v_a_2434_);
v_a_2528_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2485_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2485_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
v___jp_2479_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2478_, v_snd_2472_, v_a_2434_, v___x_2467_, v_fst_2471_, v___x_2433_, v___x_2480_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
v___y_2445_ = v___x_2481_;
goto v___jp_2444_;
}
}
}
v___jp_2444_:
{
if (lean_obj_tag(v___y_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2458_; 
v_a_2446_ = lean_ctor_get(v___y_2445_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___y_2445_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2448_ = v___y_2445_;
v_isShared_2449_ = v_isSharedCheck_2458_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___y_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2458_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
if (lean_obj_tag(v_a_2446_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; 
lean_dec(v_a_2434_);
v_a_2450_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v_a_2446_, 1);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v_a_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_del_object(v___x_2448_);
v_a_2454_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v_a_2446_, 1);
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_nat_add(v_a_2434_, v___x_2455_);
lean_dec(v_a_2434_);
v_a_2434_ = v___x_2456_;
v_b_2435_ = v_a_2454_;
goto _start;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_a_2434_);
v_a_2459_ = lean_ctor_get(v___y_2445_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___y_2445_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___y_2445_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___y_2445_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, uint8_t v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___y_2550_; uint8_t v_modified_2551_; lean_object* v_f_2552_; uint8_t v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v_args_2608_; uint8_t v_modified_2609_; uint8_t v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; uint8_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; 
if (lean_obj_tag(v_x_2538_) == 5)
{
lean_object* v_fn_2645_; lean_object* v_arg_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_fn_2645_ = lean_ctor_get(v_x_2538_, 0);
lean_inc_ref(v_fn_2645_);
v_arg_2646_ = lean_ctor_get(v_x_2538_, 1);
lean_inc_ref(v_arg_2646_);
lean_dec_ref_known(v_x_2538_, 2);
v___x_2647_ = lean_array_set(v_x_2539_, v_x_2540_, v_arg_2646_);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_sub(v_x_2540_, v___x_2648_);
lean_dec(v_x_2540_);
v_x_2538_ = v_fn_2645_;
v_x_2539_ = v___x_2647_;
v_x_2540_ = v___x_2649_;
goto _start;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
lean_dec(v_x_2540_);
v___x_2651_ = lean_array_get_size(v_x_2539_);
v___x_2652_ = lean_unsigned_to_nat(2u);
v___x_2653_ = lean_nat_dec_eq(v___x_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
v___y_2624_ = v___y_2541_;
v___y_2625_ = v___y_2542_;
v___y_2626_ = v___y_2543_;
v___y_2627_ = v___y_2544_;
v___y_2628_ = v___y_2545_;
v___y_2629_ = v___y_2546_;
v___y_2630_ = v___y_2547_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2654_ = l_Lean_instInhabitedExpr;
v___x_2655_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2656_ = l_Lean_Expr_isConstOf(v_x_2538_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2658_ = l_Lean_Expr_isConstOf(v_x_2538_, v___x_2657_);
if (v___x_2658_ == 0)
{
v___y_2624_ = v___y_2541_;
v___y_2625_ = v___y_2542_;
v___y_2626_ = v___y_2543_;
v___y_2627_ = v___y_2544_;
v___y_2628_ = v___y_2545_;
v___y_2629_ = v___y_2546_;
v___y_2630_ = v___y_2547_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_array_get(v___x_2654_, v_x_2539_, v___x_2659_);
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_array_get(v___x_2654_, v_x_2539_, v___x_2661_);
lean_dec_ref(v_x_2539_);
v___x_2663_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2538_, v___x_2660_, v___x_2662_, v_e_2537_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2663_;
}
}
else
{
lean_object* v___x_2664_; lean_object* v_prop_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_unsigned_to_nat(0u);
v_prop_2665_ = lean_array_get_borrowed(v___x_2654_, v_x_2539_, v___x_2664_);
lean_inc(v_prop_2665_);
v___x_2666_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2665_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2683_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
size_t v___x_2671_; size_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2671_ = lean_ptr_addr(v_prop_2665_);
v___x_2672_ = lean_ptr_addr(v_a_2667_);
v___x_2673_ = lean_usize_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_dec_ref(v_e_2537_);
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = lean_array_get(v___x_2654_, v_x_2539_, v___x_2674_);
lean_dec_ref(v_x_2539_);
v___x_2676_ = l_Lean_mkAppB(v_x_2538_, v_a_2667_, v___x_2675_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2676_);
v___x_2678_ = v___x_2669_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_a_2667_);
lean_dec_ref(v_x_2539_);
lean_dec_ref(v_x_2538_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v_e_2537_);
v___x_2681_ = v___x_2669_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_e_2537_);
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
lean_dec_ref(v_x_2539_);
lean_dec_ref(v_x_2538_);
lean_dec_ref(v_e_2537_);
return v___x_2666_;
}
}
}
}
v___jp_2549_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_box(0);
lean_inc_ref(v_f_2552_);
v___x_2561_ = l_Lean_Meta_getFunInfo(v_f_2552_, v___x_2560_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v_paramInfo_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2597_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v_paramInfo_2563_ = lean_ctor_get(v_a_2562_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_a_2562_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_a_2562_, 1);
lean_dec(v_unused_2598_);
v___x_2565_ = v_a_2562_;
v_isShared_2566_ = v_isSharedCheck_2597_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_paramInfo_2563_);
lean_dec(v_a_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2597_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2567_ = lean_array_get_size(v___y_2550_);
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = lean_box(v_modified_2551_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___y_2550_);
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2571_ = v___x_2565_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___y_2550_);
v___x_2571_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2567_, v_paramInfo_2563_, v___x_2568_, v___x_2571_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec_ref(v_paramInfo_2563_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2587_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_fst_2577_; uint8_t v___x_2578_; 
v_fst_2577_ = lean_ctor_get(v_a_2573_, 0);
v___x_2578_ = lean_unbox(v_fst_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2580_; 
lean_dec(v_a_2573_);
lean_dec_ref(v_f_2552_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v_e_2537_);
v___x_2580_ = v___x_2575_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_e_2537_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_dec_ref(v_e_2537_);
v_snd_2582_ = lean_ctor_get(v_a_2573_, 1);
lean_inc(v_snd_2582_);
lean_dec(v_a_2573_);
v___x_2583_ = l_Lean_mkAppN(v_f_2552_, v_snd_2582_);
lean_dec(v_snd_2582_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2583_);
v___x_2585_ = v___x_2575_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_f_2552_);
lean_dec_ref(v_e_2537_);
v_a_2588_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2572_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2572_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_f_2552_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_e_2537_);
v_a_2599_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2561_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2561_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
v___jp_2607_:
{
lean_object* v___x_2617_; 
lean_inc_ref(v_x_2538_);
v___x_2617_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2538_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; size_t v___x_2619_; size_t v___x_2620_; uint8_t v___x_2621_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = lean_ptr_addr(v_x_2538_);
v___x_2620_ = lean_ptr_addr(v_a_2618_);
v___x_2621_ = lean_usize_dec_eq(v___x_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
uint8_t v___x_2622_; 
lean_dec_ref(v_x_2538_);
v___x_2622_ = 1;
v___y_2550_ = v_args_2608_;
v_modified_2551_ = v___x_2622_;
v_f_2552_ = v_a_2618_;
v___y_2553_ = v___y_2610_;
v___y_2554_ = v___y_2611_;
v___y_2555_ = v___y_2612_;
v___y_2556_ = v___y_2613_;
v___y_2557_ = v___y_2614_;
v___y_2558_ = v___y_2615_;
v___y_2559_ = v___y_2616_;
goto v___jp_2549_;
}
else
{
lean_dec(v_a_2618_);
v___y_2550_ = v_args_2608_;
v_modified_2551_ = v_modified_2609_;
v_f_2552_ = v_x_2538_;
v___y_2553_ = v___y_2610_;
v___y_2554_ = v___y_2611_;
v___y_2555_ = v___y_2612_;
v___y_2556_ = v___y_2613_;
v___y_2557_ = v___y_2614_;
v___y_2558_ = v___y_2615_;
v___y_2559_ = v___y_2616_;
goto v___jp_2549_;
}
}
else
{
lean_dec_ref(v_args_2608_);
lean_dec_ref(v_x_2538_);
lean_dec_ref(v_e_2537_);
return v___x_2617_;
}
}
v___jp_2623_:
{
uint8_t v_modified_2631_; lean_object* v___x_2632_; uint8_t v_modified_2633_; 
v_modified_2631_ = 0;
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2633_ = l_Lean_Expr_isConstOf(v_x_2538_, v___x_2632_);
if (v_modified_2633_ == 0)
{
v_args_2608_ = v_x_2539_;
v_modified_2609_ = v_modified_2631_;
v___y_2610_ = v___y_2624_;
v___y_2611_ = v___y_2625_;
v___y_2612_ = v___y_2626_;
v___y_2613_ = v___y_2627_;
v___y_2614_ = v___y_2628_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2634_; 
lean_inc_ref(v_x_2539_);
v___x_2634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2539_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
if (lean_obj_tag(v_a_2635_) == 1)
{
lean_object* v_val_2636_; 
lean_dec_ref(v_x_2539_);
v_val_2636_ = lean_ctor_get(v_a_2635_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v_a_2635_, 1);
v_args_2608_ = v_val_2636_;
v_modified_2609_ = v_modified_2633_;
v___y_2610_ = v___y_2624_;
v___y_2611_ = v___y_2625_;
v___y_2612_ = v___y_2626_;
v___y_2613_ = v___y_2627_;
v___y_2614_ = v___y_2628_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
goto v___jp_2607_;
}
else
{
lean_dec(v_a_2635_);
v_args_2608_ = v_x_2539_;
v_modified_2609_ = v_modified_2631_;
v___y_2610_ = v___y_2624_;
v___y_2611_ = v___y_2625_;
v___y_2612_ = v___y_2626_;
v___y_2613_ = v___y_2627_;
v___y_2614_ = v___y_2628_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_x_2539_);
lean_dec_ref(v_x_2538_);
lean_dec_ref(v_e_2537_);
v_a_2637_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2634_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2634_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2684_, uint8_t v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_dummy_2693_; lean_object* v_nargs_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_dummy_2693_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2694_ = l_Lean_Expr_getAppNumArgs(v_e_2684_);
lean_inc(v_nargs_2694_);
v___x_2695_ = lean_mk_array(v_nargs_2694_, v_dummy_2693_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_sub(v_nargs_2694_, v___x_2696_);
lean_dec(v_nargs_2694_);
lean_inc_ref(v_e_2684_);
v___x_2698_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2684_, v_e_2684_, v___x_2695_, v___x_2697_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2699_, uint8_t v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v___x_2728_; 
lean_inc_ref(v_e_2699_);
v___x_2728_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2699_);
if (v___x_2728_ == 0)
{
lean_object* v_f_2729_; 
v_f_2729_ = l_Lean_Expr_getAppFn(v_e_2699_);
if (lean_obj_tag(v_f_2729_) == 4)
{
lean_object* v_declName_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_declName_2730_ = lean_ctor_get(v_f_2729_, 0);
lean_inc(v_declName_2730_);
lean_dec_ref_known(v_f_2729_, 2);
v___x_2731_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2732_ = lean_name_eq(v_declName_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_2734_ = lean_name_eq(v_declName_2730_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2736_ = lean_name_eq(v_declName_2730_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2738_ = lean_name_eq(v_declName_2730_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_2740_ = lean_name_eq(v_declName_2730_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2730_, v_a_2706_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2771_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2771_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2771_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
if (lean_obj_tag(v_a_2742_) == 1)
{
lean_object* v_val_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2744_);
v_val_2746_ = lean_ctor_get(v_a_2742_, 0);
lean_inc(v_val_2746_);
lean_dec_ref_known(v_a_2742_, 1);
lean_inc_ref(v_e_2699_);
v___x_2747_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2746_, v_e_2699_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_val_2746_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2759_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
if (lean_obj_tag(v_a_2748_) == 0)
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_e_2699_);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_e_2699_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2757_; 
lean_dec_ref(v_e_2699_);
v_val_2755_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v_a_2748_, 1);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_val_2755_);
v___x_2757_ = v___x_2750_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_val_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v_e_2699_);
v_a_2760_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2747_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2747_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_a_2742_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_e_2699_);
v___x_2769_ = v___x_2744_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_e_2699_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v_e_2699_);
v_a_2772_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2741_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2741_);
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
else
{
lean_dec(v_declName_2730_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_declName_2730_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_declName_2730_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_declName_2730_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_declName_2730_);
goto v___jp_2708_;
}
}
else
{
lean_object* v___x_2780_; 
lean_dec_ref(v_f_2729_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_e_2699_);
return v___x_2780_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_inc_ref(v_e_2699_);
v___x_2781_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2781_, 0, v_e_2699_);
v___x_2782_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2781_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2816_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2816_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2816_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
if (lean_obj_tag(v_a_2783_) == 1)
{
lean_object* v_val_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
lean_dec_ref(v_e_2699_);
v_val_2787_ = lean_ctor_get(v_a_2783_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v_a_2783_, 1);
v___x_2788_ = l_Lean_mkNatLit(v_val_2787_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2788_);
v___x_2790_ = v___x_2785_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
else
{
lean_object* v___x_2792_; 
lean_del_object(v___x_2785_);
lean_dec(v_a_2783_);
lean_inc_ref(v_e_2699_);
v___x_2792_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2699_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2807_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2807_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2807_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
if (lean_obj_tag(v_a_2793_) == 1)
{
lean_object* v_val_2797_; lean_object* v_fst_2798_; lean_object* v_snd_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_dec_ref(v_e_2699_);
v_val_2797_ = lean_ctor_get(v_a_2793_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v_a_2793_, 1);
v_fst_2798_ = lean_ctor_get(v_val_2797_, 0);
lean_inc(v_fst_2798_);
v_snd_2799_ = lean_ctor_get(v_val_2797_, 1);
lean_inc(v_snd_2799_);
lean_dec(v_val_2797_);
v___x_2800_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2798_, v_snd_2799_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2800_);
v___x_2802_ = v___x_2795_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
else
{
lean_object* v___x_2805_; 
lean_dec(v_a_2793_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_e_2699_);
v___x_2805_ = v___x_2795_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_e_2699_);
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
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v_e_2699_);
v_a_2808_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2792_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2792_);
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
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v_e_2699_);
v_a_2817_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2782_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2782_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
v___jp_2708_:
{
lean_object* v___x_2709_; 
lean_inc_ref(v_e_2699_);
v___x_2709_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2699_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
if (lean_obj_tag(v_a_2710_) == 1)
{
lean_object* v_val_2714_; lean_object* v___x_2715_; 
lean_del_object(v___x_2712_);
lean_dec_ref(v_e_2699_);
v_val_2714_ = lean_ctor_get(v_a_2710_, 0);
lean_inc(v_val_2714_);
lean_dec_ref_known(v_a_2710_, 1);
v___x_2715_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2714_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
return v___x_2715_;
}
else
{
lean_object* v___x_2717_; 
lean_dec(v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_e_2699_);
v___x_2717_ = v___x_2712_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_e_2699_);
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
lean_dec_ref(v_e_2699_);
v_a_2720_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2709_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2709_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2825_, uint8_t v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2835_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
return v___x_2836_;
}
else
{
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2837_, uint8_t v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2837_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
if (lean_obj_tag(v_a_2847_) == 0)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_e_2837_);
v_val_2848_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_ref(v_val_2848_);
lean_dec_ref_known(v_a_2847_, 1);
v___x_2849_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2848_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; 
lean_dec(v_a_2847_);
v___x_2850_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2851_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2862_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v_val_2857_; lean_object* v___x_2858_; 
lean_del_object(v___x_2855_);
lean_dec(v_a_2851_);
v_val_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc_ref(v_val_2857_);
lean_dec_ref_known(v_a_2853_, 1);
v___x_2858_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2857_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2858_;
}
else
{
lean_object* v___x_2860_; 
lean_dec(v_a_2853_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2851_);
v___x_2860_ = v___x_2855_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2851_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2851_);
v_a_2863_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2852_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2852_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
return v___x_2850_;
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v_e_2837_);
v_a_2871_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2846_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2846_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2885_, uint8_t v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
uint8_t v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___x_2904_; 
lean_inc_ref(v_e_2885_);
v___x_2904_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2885_, v_a_2890_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = l_Lean_Expr_cleanupAnnotations(v_a_2905_);
v___x_2907_ = l_Lean_Expr_isApp(v___x_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v___x_2906_);
v___y_2895_ = v_a_2886_;
v___y_2896_ = v_a_2887_;
v___y_2897_ = v_a_2888_;
v___y_2898_ = v_a_2889_;
v___y_2899_ = v_a_2890_;
v___y_2900_ = v_a_2891_;
v___y_2901_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v_arg_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_arg_2908_ = lean_ctor_get(v___x_2906_, 1);
lean_inc_ref(v_arg_2908_);
v___x_2909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2906_);
v___x_2910_ = l_Lean_Expr_isApp(v___x_2909_);
if (v___x_2910_ == 0)
{
lean_dec_ref(v___x_2909_);
lean_dec_ref(v_arg_2908_);
v___y_2895_ = v_a_2886_;
v___y_2896_ = v_a_2887_;
v___y_2897_ = v_a_2888_;
v___y_2898_ = v_a_2889_;
v___y_2899_ = v_a_2890_;
v___y_2900_ = v_a_2891_;
v___y_2901_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v_arg_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_arg_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc_ref(v_arg_2911_);
v___x_2912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2909_);
v___x_2913_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2914_ = l_Lean_Expr_isConstOf(v___x_2912_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_dec_ref(v___x_2912_);
lean_dec_ref(v_arg_2911_);
lean_dec_ref(v_arg_2908_);
v___y_2895_ = v_a_2886_;
v___y_2896_ = v_a_2887_;
v___y_2897_ = v_a_2888_;
v___y_2898_ = v_a_2889_;
v___y_2899_ = v_a_2890_;
v___y_2900_ = v_a_2891_;
v___y_2901_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2912_, v_arg_2911_, v_arg_2908_, v_e_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
return v___x_2915_;
}
}
}
}
else
{
lean_dec_ref(v_e_2885_);
return v___x_2904_;
}
v___jp_2894_:
{
uint8_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = 0;
v___x_2903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2885_, v___x_2902_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2916_, lean_object* v_00_u03b1_2917_, lean_object* v_c_2918_, lean_object* v_inst_2919_, lean_object* v_a_2920_, lean_object* v_b_2921_, uint8_t v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2918_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; uint8_t v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_n(v_a_2931_, 2);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2931_);
if (v___x_2932_ == 0)
{
uint8_t v___x_2933_; 
lean_inc(v_a_2931_);
v___x_2933_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2931_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2917_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2919_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2920_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = l_Lean_mkApp5(v_f_2916_, v_a_2935_, v_a_2931_, v_a_2937_, v_a_2939_, v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec(v_a_2935_);
lean_dec(v_a_2931_);
lean_dec_ref(v_f_2916_);
return v___x_2940_;
}
}
else
{
lean_dec(v_a_2937_);
lean_dec(v_a_2935_);
lean_dec(v_a_2931_);
lean_dec_ref(v_b_2921_);
lean_dec_ref(v_f_2916_);
return v___x_2938_;
}
}
else
{
lean_dec(v_a_2935_);
lean_dec(v_a_2931_);
lean_dec_ref(v_b_2921_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_f_2916_);
return v___x_2936_;
}
}
else
{
lean_dec(v_a_2931_);
lean_dec_ref(v_b_2921_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_inst_2919_);
lean_dec_ref(v_f_2916_);
return v___x_2934_;
}
}
else
{
lean_object* v___x_2950_; 
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_inst_2919_);
lean_dec_ref(v_00_u03b1_2917_);
lean_dec_ref(v_f_2916_);
v___x_2950_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
return v___x_2950_;
}
}
else
{
lean_object* v___x_2951_; 
lean_dec(v_a_2931_);
lean_dec_ref(v_b_2921_);
lean_dec_ref(v_inst_2919_);
lean_dec_ref(v_00_u03b1_2917_);
lean_dec_ref(v_f_2916_);
v___x_2951_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2920_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
return v___x_2951_;
}
}
else
{
lean_dec_ref(v_b_2921_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_inst_2919_);
lean_dec_ref(v_00_u03b1_2917_);
lean_dec_ref(v_f_2916_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2952_, lean_object* v_00_u03b1_2953_, lean_object* v_c_2954_, lean_object* v_a_2955_, lean_object* v_b_2956_, uint8_t v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2954_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; uint8_t v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc_n(v_a_2966_, 2);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = l_Lean_Expr_isBoolTrue(v_a_2966_);
if (v___x_2967_ == 0)
{
uint8_t v___x_2968_; 
lean_inc(v_a_2966_);
v___x_2968_ = l_Lean_Expr_isBoolFalse(v_a_2966_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2953_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2955_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = l_Lean_mkApp4(v_f_2952_, v_a_2970_, v_a_2966_, v_a_2972_, v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_dec(v_a_2972_);
lean_dec(v_a_2970_);
lean_dec(v_a_2966_);
lean_dec_ref(v_f_2952_);
return v___x_2973_;
}
}
else
{
lean_dec(v_a_2970_);
lean_dec(v_a_2966_);
lean_dec_ref(v_b_2956_);
lean_dec_ref(v_f_2952_);
return v___x_2971_;
}
}
else
{
lean_dec(v_a_2966_);
lean_dec_ref(v_b_2956_);
lean_dec_ref(v_a_2955_);
lean_dec_ref(v_f_2952_);
return v___x_2969_;
}
}
else
{
lean_object* v___x_2983_; 
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2955_);
lean_dec_ref(v_00_u03b1_2953_);
lean_dec_ref(v_f_2952_);
v___x_2983_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
return v___x_2983_;
}
}
else
{
lean_object* v___x_2984_; 
lean_dec(v_a_2966_);
lean_dec_ref(v_b_2956_);
lean_dec_ref(v_00_u03b1_2953_);
lean_dec_ref(v_f_2952_);
v___x_2984_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2955_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
return v___x_2984_;
}
}
else
{
lean_dec_ref(v_b_2956_);
lean_dec_ref(v_a_2955_);
lean_dec_ref(v_00_u03b1_2953_);
lean_dec_ref(v_f_2952_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2985_, uint8_t v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; uint8_t v___y_3002_; uint8_t v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___x_3030_; 
lean_inc_ref(v_e_2985_);
v___x_3030_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2985_, v_a_2990_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = l_Lean_Expr_cleanupAnnotations(v_a_3031_);
v___x_3033_ = l_Lean_Expr_isApp(v___x_3032_);
if (v___x_3033_ == 0)
{
lean_dec_ref(v___x_3032_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_arg_3034_ = lean_ctor_get(v___x_3032_, 1);
lean_inc_ref(v_arg_3034_);
v___x_3035_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3032_);
v___x_3036_ = l_Lean_Expr_isApp(v___x_3035_);
if (v___x_3036_ == 0)
{
lean_dec_ref(v___x_3035_);
lean_dec_ref(v_arg_3034_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v_arg_3037_ = lean_ctor_get(v___x_3035_, 1);
lean_inc_ref(v_arg_3037_);
v___x_3038_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3035_);
v___x_3039_ = l_Lean_Expr_isApp(v___x_3038_);
if (v___x_3039_ == 0)
{
lean_dec_ref(v___x_3038_);
lean_dec_ref(v_arg_3037_);
lean_dec_ref(v_arg_3034_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_arg_3040_ = lean_ctor_get(v___x_3038_, 1);
lean_inc_ref(v_arg_3040_);
v___x_3041_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3038_);
v___x_3042_ = l_Lean_Expr_isApp(v___x_3041_);
if (v___x_3042_ == 0)
{
lean_dec_ref(v___x_3041_);
lean_dec_ref(v_arg_3040_);
lean_dec_ref(v_arg_3037_);
lean_dec_ref(v_arg_3034_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v_arg_3043_ = lean_ctor_get(v___x_3041_, 1);
lean_inc_ref(v_arg_3043_);
v___x_3044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3041_);
v___x_3045_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3046_ = l_Lean_Expr_isConstOf(v___x_3044_, v___x_3045_);
if (v___x_3046_ == 0)
{
uint8_t v___x_3047_; 
v___x_3047_ = l_Lean_Expr_isApp(v___x_3044_);
if (v___x_3047_ == 0)
{
lean_dec_ref(v___x_3044_);
lean_dec_ref(v_arg_3043_);
lean_dec_ref(v_arg_3040_);
lean_dec_ref(v_arg_3037_);
lean_dec_ref(v_arg_3034_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_arg_3048_ = lean_ctor_get(v___x_3044_, 1);
lean_inc_ref(v_arg_3048_);
v___x_3049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3044_);
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3051_ = l_Lean_Expr_isConstOf(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_dec_ref(v___x_3049_);
lean_dec_ref(v_arg_3048_);
lean_dec_ref(v_arg_3043_);
lean_dec_ref(v_arg_3040_);
lean_dec_ref(v_arg_3037_);
lean_dec_ref(v_arg_3034_);
v___y_3019_ = v_a_2986_;
v___y_3020_ = v_a_2987_;
v___y_3021_ = v_a_2988_;
v___y_3022_ = v_a_2989_;
v___y_3023_ = v_a_2990_;
v___y_3024_ = v_a_2991_;
v___y_3025_ = v_a_2992_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3052_; 
lean_dec_ref(v_e_2985_);
v___x_3052_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3049_, v_arg_3048_, v_arg_3043_, v_arg_3040_, v_arg_3037_, v_arg_3034_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
return v___x_3052_;
}
}
}
else
{
lean_object* v___x_3053_; 
lean_dec_ref(v_e_2985_);
v___x_3053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3044_, v_arg_3043_, v_arg_3040_, v_arg_3037_, v_arg_3034_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
return v___x_3053_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2985_);
return v___x_3030_;
}
v___jp_2994_:
{
if (lean_obj_tag(v___y_2995_) == 4)
{
lean_object* v_declName_3003_; lean_object* v___x_3004_; 
v_declName_3003_ = lean_ctor_get(v___y_2995_, 0);
lean_inc(v_declName_3003_);
lean_dec_ref_known(v___y_2995_, 2);
v___x_3004_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3003_, v___y_3001_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; uint8_t v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = lean_unbox(v_a_3005_);
lean_dec(v_a_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2985_, v___y_3002_, v___y_3000_, v___y_2998_, v___y_2997_, v___y_2996_, v___y_2999_, v___y_3001_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; 
v___x_3008_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2985_, v___y_3002_, v___y_3000_, v___y_2998_, v___y_2997_, v___y_2996_, v___y_2999_, v___y_3001_);
return v___x_3008_;
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_e_2985_);
v_a_3009_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3004_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3004_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v___x_3017_; 
lean_dec_ref(v___y_2995_);
v___x_3017_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2985_, v___y_3002_, v___y_3000_, v___y_2998_, v___y_2997_, v___y_2996_, v___y_2999_, v___y_3001_);
return v___x_3017_;
}
}
v___jp_3018_:
{
lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = l_Lean_Expr_getAppFn(v_e_2985_);
v___x_3027_ = l_Lean_Expr_isLambda(v___x_3026_);
if (v___x_3027_ == 0)
{
v___y_2995_ = v___x_3026_;
v___y_2996_ = v___y_3023_;
v___y_2997_ = v___y_3022_;
v___y_2998_ = v___y_3021_;
v___y_2999_ = v___y_3024_;
v___y_3000_ = v___y_3020_;
v___y_3001_ = v___y_3025_;
v___y_3002_ = v___y_3019_;
goto v___jp_2994_;
}
else
{
if (v___y_3019_ == 0)
{
v___y_2995_ = v___x_3026_;
v___y_2996_ = v___y_3023_;
v___y_2997_ = v___y_3022_;
v___y_2998_ = v___y_3021_;
v___y_2999_ = v___y_3024_;
v___y_3000_ = v___y_3020_;
v___y_3001_ = v___y_3025_;
v___y_3002_ = v___y_3019_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref(v___x_3026_);
v___x_3028_ = l_Lean_Expr_headBeta(v_e_2985_);
v___x_3029_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3028_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3029_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3058_ = lean_unsigned_to_nat(18u);
v___x_3059_ = lean_unsigned_to_nat(1913u);
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3061_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3062_ = l_mkPanicMessageWithDecl(v___x_3061_, v___x_3060_, v___x_3059_, v___x_3058_, v___x_3057_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3063_, uint8_t v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = l_Lean_Expr_projExpr_x21(v_e_3063_);
v___x_3073_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3072_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___y_3076_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
if (lean_obj_tag(v_e_3063_) == 11)
{
lean_object* v_typeName_3098_; lean_object* v_idx_3099_; lean_object* v_struct_3100_; size_t v___x_3101_; size_t v___x_3102_; uint8_t v___x_3103_; 
v_typeName_3098_ = lean_ctor_get(v_e_3063_, 0);
v_idx_3099_ = lean_ctor_get(v_e_3063_, 1);
v_struct_3100_ = lean_ctor_get(v_e_3063_, 2);
v___x_3101_ = lean_ptr_addr(v_struct_3100_);
v___x_3102_ = lean_ptr_addr(v_a_3074_);
v___x_3103_ = lean_usize_dec_eq(v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_inc(v_idx_3099_);
lean_inc(v_typeName_3098_);
lean_dec_ref_known(v_e_3063_, 3);
v___x_3104_ = l_Lean_Expr_proj___override(v_typeName_3098_, v_idx_3099_, v_a_3074_);
v___y_3076_ = v___x_3104_;
goto v___jp_3075_;
}
else
{
lean_dec(v_a_3074_);
v___y_3076_ = v_e_3063_;
goto v___jp_3075_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_e_3063_);
v___x_3105_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3106_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3105_);
v___y_3076_ = v___x_3106_;
goto v___jp_3075_;
}
v___jp_3075_:
{
lean_object* v___x_3077_; 
lean_inc_ref(v___y_3076_);
v___x_3077_ = l_Lean_Meta_reduceProj_x3f(v___y_3076_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3089_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
if (lean_obj_tag(v_a_3078_) == 0)
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___y_3076_);
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___y_3076_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3087_; 
lean_dec_ref(v___y_3076_);
v_val_3085_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_val_3085_);
lean_dec_ref_known(v_a_3078_, 1);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v_val_3085_);
v___x_3087_ = v___x_3080_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_val_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec_ref(v___y_3076_);
v_a_3090_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3077_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3077_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3063_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3107_, uint8_t v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
switch(lean_obj_tag(v_e_3107_))
{
case 7:
{
lean_object* v___x_3116_; 
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3108_ == 0)
{
lean_object* v___x_3117_; lean_object* v_canon_3118_; lean_object* v_cache_3119_; lean_object* v___x_3120_; 
v___x_3117_ = lean_st_ref_get(v_a_3110_);
v_canon_3118_ = lean_ctor_get(v___x_3117_, 10);
lean_inc_ref(v_canon_3118_);
lean_dec(v___x_3117_);
v_cache_3119_ = lean_ctor_get(v_canon_3118_, 0);
lean_inc_ref(v_cache_3119_);
lean_dec_ref(v_canon_3118_);
v___x_3120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3119_, v_e_3107_);
lean_dec_ref(v_cache_3119_);
if (lean_obj_tag(v___x_3120_) == 1)
{
lean_object* v_val_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_val_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 0);
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_val_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
else
{
lean_object* v___x_3129_; 
lean_dec(v___x_3120_);
lean_inc_ref(v_e_3107_);
v___x_3129_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3116_, v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3169_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3169_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3169_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v_canon_3135_; lean_object* v_share_3136_; lean_object* v_maxFVar_3137_; lean_object* v_proofInstInfo_3138_; lean_object* v_proofInstInfoFVar_3139_; lean_object* v_inferType_3140_; lean_object* v_getLevel_3141_; lean_object* v_congrInfo_3142_; lean_object* v_defEqI_3143_; lean_object* v_extensions_3144_; lean_object* v_issues_3145_; lean_object* v_instanceOverrides_3146_; uint8_t v_debug_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3168_; 
v___x_3134_ = lean_st_ref_take(v_a_3110_);
v_canon_3135_ = lean_ctor_get(v___x_3134_, 10);
v_share_3136_ = lean_ctor_get(v___x_3134_, 0);
v_maxFVar_3137_ = lean_ctor_get(v___x_3134_, 1);
v_proofInstInfo_3138_ = lean_ctor_get(v___x_3134_, 2);
v_proofInstInfoFVar_3139_ = lean_ctor_get(v___x_3134_, 3);
v_inferType_3140_ = lean_ctor_get(v___x_3134_, 4);
v_getLevel_3141_ = lean_ctor_get(v___x_3134_, 5);
v_congrInfo_3142_ = lean_ctor_get(v___x_3134_, 6);
v_defEqI_3143_ = lean_ctor_get(v___x_3134_, 7);
v_extensions_3144_ = lean_ctor_get(v___x_3134_, 8);
v_issues_3145_ = lean_ctor_get(v___x_3134_, 9);
v_instanceOverrides_3146_ = lean_ctor_get(v___x_3134_, 11);
v_debug_3147_ = lean_ctor_get_uint8(v___x_3134_, sizeof(void*)*12);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3149_ = v___x_3134_;
v_isShared_3150_ = v_isSharedCheck_3168_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_instanceOverrides_3146_);
lean_inc(v_canon_3135_);
lean_inc(v_issues_3145_);
lean_inc(v_extensions_3144_);
lean_inc(v_defEqI_3143_);
lean_inc(v_congrInfo_3142_);
lean_inc(v_getLevel_3141_);
lean_inc(v_inferType_3140_);
lean_inc(v_proofInstInfoFVar_3139_);
lean_inc(v_proofInstInfo_3138_);
lean_inc(v_maxFVar_3137_);
lean_inc(v_share_3136_);
lean_dec(v___x_3134_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3168_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_cache_3151_; lean_object* v_cacheInType_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3167_; 
v_cache_3151_ = lean_ctor_get(v_canon_3135_, 0);
v_cacheInType_3152_ = lean_ctor_get(v_canon_3135_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_canon_3135_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3154_ = v_canon_3135_;
v_isShared_3155_ = v_isSharedCheck_3167_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_cacheInType_3152_);
lean_inc(v_cache_3151_);
lean_dec(v_canon_3135_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3167_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
lean_inc(v_a_3130_);
v___x_3156_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3151_, v_e_3107_, v_a_3130_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3156_);
v___x_3158_ = v___x_3154_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_cacheInType_3152_);
v___x_3158_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3160_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 10, v___x_3158_);
v___x_3160_ = v___x_3149_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_share_3136_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_maxFVar_3137_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_proofInstInfo_3138_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_proofInstInfoFVar_3139_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_inferType_3140_);
lean_ctor_set(v_reuseFailAlloc_3165_, 5, v_getLevel_3141_);
lean_ctor_set(v_reuseFailAlloc_3165_, 6, v_congrInfo_3142_);
lean_ctor_set(v_reuseFailAlloc_3165_, 7, v_defEqI_3143_);
lean_ctor_set(v_reuseFailAlloc_3165_, 8, v_extensions_3144_);
lean_ctor_set(v_reuseFailAlloc_3165_, 9, v_issues_3145_);
lean_ctor_set(v_reuseFailAlloc_3165_, 10, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3165_, 11, v_instanceOverrides_3146_);
lean_ctor_set_uint8(v_reuseFailAlloc_3165_, sizeof(void*)*12, v_debug_3147_);
v___x_3160_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3161_ = lean_st_ref_put(v_a_3110_, v___x_3160_);
if (v_isShared_3133_ == 0)
{
v___x_3163_ = v___x_3132_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3130_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3129_;
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v_canon_3171_; lean_object* v_cacheInType_3172_; lean_object* v___x_3173_; 
v___x_3170_ = lean_st_ref_get(v_a_3110_);
v_canon_3171_ = lean_ctor_get(v___x_3170_, 10);
lean_inc_ref(v_canon_3171_);
lean_dec(v___x_3170_);
v_cacheInType_3172_ = lean_ctor_get(v_canon_3171_, 1);
lean_inc_ref(v_cacheInType_3172_);
lean_dec_ref(v_canon_3171_);
v___x_3173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3172_, v_e_3107_);
lean_dec_ref(v_cacheInType_3172_);
if (lean_obj_tag(v___x_3173_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_val_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 0);
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_val_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
else
{
lean_object* v___x_3182_; 
lean_dec(v___x_3173_);
lean_inc_ref(v_e_3107_);
v___x_3182_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3116_, v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3222_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3222_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3222_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v_canon_3188_; lean_object* v_share_3189_; lean_object* v_maxFVar_3190_; lean_object* v_proofInstInfo_3191_; lean_object* v_proofInstInfoFVar_3192_; lean_object* v_inferType_3193_; lean_object* v_getLevel_3194_; lean_object* v_congrInfo_3195_; lean_object* v_defEqI_3196_; lean_object* v_extensions_3197_; lean_object* v_issues_3198_; lean_object* v_instanceOverrides_3199_; uint8_t v_debug_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3221_; 
v___x_3187_ = lean_st_ref_take(v_a_3110_);
v_canon_3188_ = lean_ctor_get(v___x_3187_, 10);
v_share_3189_ = lean_ctor_get(v___x_3187_, 0);
v_maxFVar_3190_ = lean_ctor_get(v___x_3187_, 1);
v_proofInstInfo_3191_ = lean_ctor_get(v___x_3187_, 2);
v_proofInstInfoFVar_3192_ = lean_ctor_get(v___x_3187_, 3);
v_inferType_3193_ = lean_ctor_get(v___x_3187_, 4);
v_getLevel_3194_ = lean_ctor_get(v___x_3187_, 5);
v_congrInfo_3195_ = lean_ctor_get(v___x_3187_, 6);
v_defEqI_3196_ = lean_ctor_get(v___x_3187_, 7);
v_extensions_3197_ = lean_ctor_get(v___x_3187_, 8);
v_issues_3198_ = lean_ctor_get(v___x_3187_, 9);
v_instanceOverrides_3199_ = lean_ctor_get(v___x_3187_, 11);
v_debug_3200_ = lean_ctor_get_uint8(v___x_3187_, sizeof(void*)*12);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3202_ = v___x_3187_;
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_instanceOverrides_3199_);
lean_inc(v_canon_3188_);
lean_inc(v_issues_3198_);
lean_inc(v_extensions_3197_);
lean_inc(v_defEqI_3196_);
lean_inc(v_congrInfo_3195_);
lean_inc(v_getLevel_3194_);
lean_inc(v_inferType_3193_);
lean_inc(v_proofInstInfoFVar_3192_);
lean_inc(v_proofInstInfo_3191_);
lean_inc(v_maxFVar_3190_);
lean_inc(v_share_3189_);
lean_dec(v___x_3187_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_cache_3204_; lean_object* v_cacheInType_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3220_; 
v_cache_3204_ = lean_ctor_get(v_canon_3188_, 0);
v_cacheInType_3205_ = lean_ctor_get(v_canon_3188_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_canon_3188_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3207_ = v_canon_3188_;
v_isShared_3208_ = v_isSharedCheck_3220_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_cacheInType_3205_);
lean_inc(v_cache_3204_);
lean_dec(v_canon_3188_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3220_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
lean_inc(v_a_3183_);
v___x_3209_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3205_, v_e_3107_, v_a_3183_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3209_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_cache_3204_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 10, v___x_3211_);
v___x_3213_ = v___x_3202_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_share_3189_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_maxFVar_3190_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_proofInstInfo_3191_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_proofInstInfoFVar_3192_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_inferType_3193_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_getLevel_3194_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_congrInfo_3195_);
lean_ctor_set(v_reuseFailAlloc_3218_, 7, v_defEqI_3196_);
lean_ctor_set(v_reuseFailAlloc_3218_, 8, v_extensions_3197_);
lean_ctor_set(v_reuseFailAlloc_3218_, 9, v_issues_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 10, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3218_, 11, v_instanceOverrides_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*12, v_debug_3200_);
v___x_3213_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = lean_st_ref_put(v_a_3110_, v___x_3213_);
if (v_isShared_3186_ == 0)
{
v___x_3216_ = v___x_3185_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3183_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3182_;
}
}
}
}
case 6:
{
if (v_a_3108_ == 0)
{
lean_object* v___x_3223_; lean_object* v_canon_3224_; lean_object* v_cache_3225_; lean_object* v___x_3226_; 
v___x_3223_ = lean_st_ref_get(v_a_3110_);
v_canon_3224_ = lean_ctor_get(v___x_3223_, 10);
lean_inc_ref(v_canon_3224_);
lean_dec(v___x_3223_);
v_cache_3225_ = lean_ctor_get(v_canon_3224_, 0);
lean_inc_ref(v_cache_3225_);
lean_dec_ref(v_canon_3224_);
v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3225_, v_e_3107_);
lean_dec_ref(v_cache_3225_);
if (lean_obj_tag(v___x_3226_) == 1)
{
lean_object* v_val_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_val_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 0);
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_val_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v___x_3235_; 
lean_dec(v___x_3226_);
lean_inc_ref(v_e_3107_);
v___x_3235_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3275_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3275_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3275_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v_canon_3241_; lean_object* v_share_3242_; lean_object* v_maxFVar_3243_; lean_object* v_proofInstInfo_3244_; lean_object* v_proofInstInfoFVar_3245_; lean_object* v_inferType_3246_; lean_object* v_getLevel_3247_; lean_object* v_congrInfo_3248_; lean_object* v_defEqI_3249_; lean_object* v_extensions_3250_; lean_object* v_issues_3251_; lean_object* v_instanceOverrides_3252_; uint8_t v_debug_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3274_; 
v___x_3240_ = lean_st_ref_take(v_a_3110_);
v_canon_3241_ = lean_ctor_get(v___x_3240_, 10);
v_share_3242_ = lean_ctor_get(v___x_3240_, 0);
v_maxFVar_3243_ = lean_ctor_get(v___x_3240_, 1);
v_proofInstInfo_3244_ = lean_ctor_get(v___x_3240_, 2);
v_proofInstInfoFVar_3245_ = lean_ctor_get(v___x_3240_, 3);
v_inferType_3246_ = lean_ctor_get(v___x_3240_, 4);
v_getLevel_3247_ = lean_ctor_get(v___x_3240_, 5);
v_congrInfo_3248_ = lean_ctor_get(v___x_3240_, 6);
v_defEqI_3249_ = lean_ctor_get(v___x_3240_, 7);
v_extensions_3250_ = lean_ctor_get(v___x_3240_, 8);
v_issues_3251_ = lean_ctor_get(v___x_3240_, 9);
v_instanceOverrides_3252_ = lean_ctor_get(v___x_3240_, 11);
v_debug_3253_ = lean_ctor_get_uint8(v___x_3240_, sizeof(void*)*12);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3255_ = v___x_3240_;
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_instanceOverrides_3252_);
lean_inc(v_canon_3241_);
lean_inc(v_issues_3251_);
lean_inc(v_extensions_3250_);
lean_inc(v_defEqI_3249_);
lean_inc(v_congrInfo_3248_);
lean_inc(v_getLevel_3247_);
lean_inc(v_inferType_3246_);
lean_inc(v_proofInstInfoFVar_3245_);
lean_inc(v_proofInstInfo_3244_);
lean_inc(v_maxFVar_3243_);
lean_inc(v_share_3242_);
lean_dec(v___x_3240_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_cache_3257_; lean_object* v_cacheInType_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3273_; 
v_cache_3257_ = lean_ctor_get(v_canon_3241_, 0);
v_cacheInType_3258_ = lean_ctor_get(v_canon_3241_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_canon_3241_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3260_ = v_canon_3241_;
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_cacheInType_3258_);
lean_inc(v_cache_3257_);
lean_dec(v_canon_3241_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_inc(v_a_3236_);
v___x_3262_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3257_, v_e_3107_, v_a_3236_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_cacheInType_3258_);
v___x_3264_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3266_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 10, v___x_3264_);
v___x_3266_ = v___x_3255_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_share_3242_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_maxFVar_3243_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_proofInstInfo_3244_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_proofInstInfoFVar_3245_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_inferType_3246_);
lean_ctor_set(v_reuseFailAlloc_3271_, 5, v_getLevel_3247_);
lean_ctor_set(v_reuseFailAlloc_3271_, 6, v_congrInfo_3248_);
lean_ctor_set(v_reuseFailAlloc_3271_, 7, v_defEqI_3249_);
lean_ctor_set(v_reuseFailAlloc_3271_, 8, v_extensions_3250_);
lean_ctor_set(v_reuseFailAlloc_3271_, 9, v_issues_3251_);
lean_ctor_set(v_reuseFailAlloc_3271_, 10, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3271_, 11, v_instanceOverrides_3252_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*12, v_debug_3253_);
v___x_3266_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3267_ = lean_st_ref_put(v_a_3110_, v___x_3266_);
if (v_isShared_3239_ == 0)
{
v___x_3269_ = v___x_3238_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3236_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3235_;
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v_canon_3277_; lean_object* v_cacheInType_3278_; lean_object* v___x_3279_; 
v___x_3276_ = lean_st_ref_get(v_a_3110_);
v_canon_3277_ = lean_ctor_get(v___x_3276_, 10);
lean_inc_ref(v_canon_3277_);
lean_dec(v___x_3276_);
v_cacheInType_3278_ = lean_ctor_get(v_canon_3277_, 1);
lean_inc_ref(v_cacheInType_3278_);
lean_dec_ref(v_canon_3277_);
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3278_, v_e_3107_);
lean_dec_ref(v_cacheInType_3278_);
if (lean_obj_tag(v___x_3279_) == 1)
{
lean_object* v_val_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_val_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 0);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_val_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v___x_3288_; 
lean_dec(v___x_3279_);
lean_inc_ref(v_e_3107_);
v___x_3288_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3328_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3328_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3328_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v_canon_3294_; lean_object* v_share_3295_; lean_object* v_maxFVar_3296_; lean_object* v_proofInstInfo_3297_; lean_object* v_proofInstInfoFVar_3298_; lean_object* v_inferType_3299_; lean_object* v_getLevel_3300_; lean_object* v_congrInfo_3301_; lean_object* v_defEqI_3302_; lean_object* v_extensions_3303_; lean_object* v_issues_3304_; lean_object* v_instanceOverrides_3305_; uint8_t v_debug_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3327_; 
v___x_3293_ = lean_st_ref_take(v_a_3110_);
v_canon_3294_ = lean_ctor_get(v___x_3293_, 10);
v_share_3295_ = lean_ctor_get(v___x_3293_, 0);
v_maxFVar_3296_ = lean_ctor_get(v___x_3293_, 1);
v_proofInstInfo_3297_ = lean_ctor_get(v___x_3293_, 2);
v_proofInstInfoFVar_3298_ = lean_ctor_get(v___x_3293_, 3);
v_inferType_3299_ = lean_ctor_get(v___x_3293_, 4);
v_getLevel_3300_ = lean_ctor_get(v___x_3293_, 5);
v_congrInfo_3301_ = lean_ctor_get(v___x_3293_, 6);
v_defEqI_3302_ = lean_ctor_get(v___x_3293_, 7);
v_extensions_3303_ = lean_ctor_get(v___x_3293_, 8);
v_issues_3304_ = lean_ctor_get(v___x_3293_, 9);
v_instanceOverrides_3305_ = lean_ctor_get(v___x_3293_, 11);
v_debug_3306_ = lean_ctor_get_uint8(v___x_3293_, sizeof(void*)*12);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3308_ = v___x_3293_;
v_isShared_3309_ = v_isSharedCheck_3327_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_instanceOverrides_3305_);
lean_inc(v_canon_3294_);
lean_inc(v_issues_3304_);
lean_inc(v_extensions_3303_);
lean_inc(v_defEqI_3302_);
lean_inc(v_congrInfo_3301_);
lean_inc(v_getLevel_3300_);
lean_inc(v_inferType_3299_);
lean_inc(v_proofInstInfoFVar_3298_);
lean_inc(v_proofInstInfo_3297_);
lean_inc(v_maxFVar_3296_);
lean_inc(v_share_3295_);
lean_dec(v___x_3293_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3327_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_cache_3310_; lean_object* v_cacheInType_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3326_; 
v_cache_3310_ = lean_ctor_get(v_canon_3294_, 0);
v_cacheInType_3311_ = lean_ctor_get(v_canon_3294_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_canon_3294_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3313_ = v_canon_3294_;
v_isShared_3314_ = v_isSharedCheck_3326_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_cacheInType_3311_);
lean_inc(v_cache_3310_);
lean_dec(v_canon_3294_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3326_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_inc(v_a_3289_);
v___x_3315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3311_, v_e_3107_, v_a_3289_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_cache_3310_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 10, v___x_3317_);
v___x_3319_ = v___x_3308_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_share_3295_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_maxFVar_3296_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_proofInstInfo_3297_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_proofInstInfoFVar_3298_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_inferType_3299_);
lean_ctor_set(v_reuseFailAlloc_3324_, 5, v_getLevel_3300_);
lean_ctor_set(v_reuseFailAlloc_3324_, 6, v_congrInfo_3301_);
lean_ctor_set(v_reuseFailAlloc_3324_, 7, v_defEqI_3302_);
lean_ctor_set(v_reuseFailAlloc_3324_, 8, v_extensions_3303_);
lean_ctor_set(v_reuseFailAlloc_3324_, 9, v_issues_3304_);
lean_ctor_set(v_reuseFailAlloc_3324_, 10, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3324_, 11, v_instanceOverrides_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3324_, sizeof(void*)*12, v_debug_3306_);
v___x_3319_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = lean_st_ref_put(v_a_3110_, v___x_3319_);
if (v_isShared_3292_ == 0)
{
v___x_3322_ = v___x_3291_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3289_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3288_;
}
}
}
}
case 8:
{
lean_object* v___x_3329_; 
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3108_ == 0)
{
lean_object* v___x_3330_; lean_object* v_canon_3331_; lean_object* v_cache_3332_; lean_object* v___x_3333_; 
v___x_3330_ = lean_st_ref_get(v_a_3110_);
v_canon_3331_ = lean_ctor_get(v___x_3330_, 10);
lean_inc_ref(v_canon_3331_);
lean_dec(v___x_3330_);
v_cache_3332_ = lean_ctor_get(v_canon_3331_, 0);
lean_inc_ref(v_cache_3332_);
lean_dec_ref(v_canon_3331_);
v___x_3333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3332_, v_e_3107_);
lean_dec_ref(v_cache_3332_);
if (lean_obj_tag(v___x_3333_) == 1)
{
lean_object* v_val_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref_known(v_e_3107_, 4);
v_val_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_val_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 0);
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_val_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v___x_3342_; 
lean_dec(v___x_3333_);
lean_inc_ref(v_e_3107_);
v___x_3342_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3329_, v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3382_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3382_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3382_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v_canon_3348_; lean_object* v_share_3349_; lean_object* v_maxFVar_3350_; lean_object* v_proofInstInfo_3351_; lean_object* v_proofInstInfoFVar_3352_; lean_object* v_inferType_3353_; lean_object* v_getLevel_3354_; lean_object* v_congrInfo_3355_; lean_object* v_defEqI_3356_; lean_object* v_extensions_3357_; lean_object* v_issues_3358_; lean_object* v_instanceOverrides_3359_; uint8_t v_debug_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3381_; 
v___x_3347_ = lean_st_ref_take(v_a_3110_);
v_canon_3348_ = lean_ctor_get(v___x_3347_, 10);
v_share_3349_ = lean_ctor_get(v___x_3347_, 0);
v_maxFVar_3350_ = lean_ctor_get(v___x_3347_, 1);
v_proofInstInfo_3351_ = lean_ctor_get(v___x_3347_, 2);
v_proofInstInfoFVar_3352_ = lean_ctor_get(v___x_3347_, 3);
v_inferType_3353_ = lean_ctor_get(v___x_3347_, 4);
v_getLevel_3354_ = lean_ctor_get(v___x_3347_, 5);
v_congrInfo_3355_ = lean_ctor_get(v___x_3347_, 6);
v_defEqI_3356_ = lean_ctor_get(v___x_3347_, 7);
v_extensions_3357_ = lean_ctor_get(v___x_3347_, 8);
v_issues_3358_ = lean_ctor_get(v___x_3347_, 9);
v_instanceOverrides_3359_ = lean_ctor_get(v___x_3347_, 11);
v_debug_3360_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*12);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3362_ = v___x_3347_;
v_isShared_3363_ = v_isSharedCheck_3381_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_instanceOverrides_3359_);
lean_inc(v_canon_3348_);
lean_inc(v_issues_3358_);
lean_inc(v_extensions_3357_);
lean_inc(v_defEqI_3356_);
lean_inc(v_congrInfo_3355_);
lean_inc(v_getLevel_3354_);
lean_inc(v_inferType_3353_);
lean_inc(v_proofInstInfoFVar_3352_);
lean_inc(v_proofInstInfo_3351_);
lean_inc(v_maxFVar_3350_);
lean_inc(v_share_3349_);
lean_dec(v___x_3347_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3381_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_cache_3364_; lean_object* v_cacheInType_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3380_; 
v_cache_3364_ = lean_ctor_get(v_canon_3348_, 0);
v_cacheInType_3365_ = lean_ctor_get(v_canon_3348_, 1);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_canon_3348_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3367_ = v_canon_3348_;
v_isShared_3368_ = v_isSharedCheck_3380_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_cacheInType_3365_);
lean_inc(v_cache_3364_);
lean_dec(v_canon_3348_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3380_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
lean_inc(v_a_3343_);
v___x_3369_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3364_, v_e_3107_, v_a_3343_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3369_);
v___x_3371_ = v___x_3367_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_cacheInType_3365_);
v___x_3371_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 10, v___x_3371_);
v___x_3373_ = v___x_3362_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_share_3349_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_maxFVar_3350_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_proofInstInfo_3351_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_proofInstInfoFVar_3352_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_inferType_3353_);
lean_ctor_set(v_reuseFailAlloc_3378_, 5, v_getLevel_3354_);
lean_ctor_set(v_reuseFailAlloc_3378_, 6, v_congrInfo_3355_);
lean_ctor_set(v_reuseFailAlloc_3378_, 7, v_defEqI_3356_);
lean_ctor_set(v_reuseFailAlloc_3378_, 8, v_extensions_3357_);
lean_ctor_set(v_reuseFailAlloc_3378_, 9, v_issues_3358_);
lean_ctor_set(v_reuseFailAlloc_3378_, 10, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3378_, 11, v_instanceOverrides_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3378_, sizeof(void*)*12, v_debug_3360_);
v___x_3373_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3374_ = lean_st_ref_put(v_a_3110_, v___x_3373_);
if (v_isShared_3346_ == 0)
{
v___x_3376_ = v___x_3345_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3343_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 4);
return v___x_3342_;
}
}
}
else
{
lean_object* v___x_3383_; lean_object* v_canon_3384_; lean_object* v_cacheInType_3385_; lean_object* v___x_3386_; 
v___x_3383_ = lean_st_ref_get(v_a_3110_);
v_canon_3384_ = lean_ctor_get(v___x_3383_, 10);
lean_inc_ref(v_canon_3384_);
lean_dec(v___x_3383_);
v_cacheInType_3385_ = lean_ctor_get(v_canon_3384_, 1);
lean_inc_ref(v_cacheInType_3385_);
lean_dec_ref(v_canon_3384_);
v___x_3386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3385_, v_e_3107_);
lean_dec_ref(v_cacheInType_3385_);
if (lean_obj_tag(v___x_3386_) == 1)
{
lean_object* v_val_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref_known(v_e_3107_, 4);
v_val_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_val_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 0);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_val_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v___x_3386_);
lean_inc_ref(v_e_3107_);
v___x_3395_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3329_, v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3435_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3435_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3435_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v_canon_3401_; lean_object* v_share_3402_; lean_object* v_maxFVar_3403_; lean_object* v_proofInstInfo_3404_; lean_object* v_proofInstInfoFVar_3405_; lean_object* v_inferType_3406_; lean_object* v_getLevel_3407_; lean_object* v_congrInfo_3408_; lean_object* v_defEqI_3409_; lean_object* v_extensions_3410_; lean_object* v_issues_3411_; lean_object* v_instanceOverrides_3412_; uint8_t v_debug_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3434_; 
v___x_3400_ = lean_st_ref_take(v_a_3110_);
v_canon_3401_ = lean_ctor_get(v___x_3400_, 10);
v_share_3402_ = lean_ctor_get(v___x_3400_, 0);
v_maxFVar_3403_ = lean_ctor_get(v___x_3400_, 1);
v_proofInstInfo_3404_ = lean_ctor_get(v___x_3400_, 2);
v_proofInstInfoFVar_3405_ = lean_ctor_get(v___x_3400_, 3);
v_inferType_3406_ = lean_ctor_get(v___x_3400_, 4);
v_getLevel_3407_ = lean_ctor_get(v___x_3400_, 5);
v_congrInfo_3408_ = lean_ctor_get(v___x_3400_, 6);
v_defEqI_3409_ = lean_ctor_get(v___x_3400_, 7);
v_extensions_3410_ = lean_ctor_get(v___x_3400_, 8);
v_issues_3411_ = lean_ctor_get(v___x_3400_, 9);
v_instanceOverrides_3412_ = lean_ctor_get(v___x_3400_, 11);
v_debug_3413_ = lean_ctor_get_uint8(v___x_3400_, sizeof(void*)*12);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3415_ = v___x_3400_;
v_isShared_3416_ = v_isSharedCheck_3434_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_instanceOverrides_3412_);
lean_inc(v_canon_3401_);
lean_inc(v_issues_3411_);
lean_inc(v_extensions_3410_);
lean_inc(v_defEqI_3409_);
lean_inc(v_congrInfo_3408_);
lean_inc(v_getLevel_3407_);
lean_inc(v_inferType_3406_);
lean_inc(v_proofInstInfoFVar_3405_);
lean_inc(v_proofInstInfo_3404_);
lean_inc(v_maxFVar_3403_);
lean_inc(v_share_3402_);
lean_dec(v___x_3400_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3434_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_cache_3417_; lean_object* v_cacheInType_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3433_; 
v_cache_3417_ = lean_ctor_get(v_canon_3401_, 0);
v_cacheInType_3418_ = lean_ctor_get(v_canon_3401_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_canon_3401_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3420_ = v_canon_3401_;
v_isShared_3421_ = v_isSharedCheck_3433_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_cacheInType_3418_);
lean_inc(v_cache_3417_);
lean_dec(v_canon_3401_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3433_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_inc(v_a_3396_);
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3418_, v_e_3107_, v_a_3396_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_cache_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 10, v___x_3424_);
v___x_3426_ = v___x_3415_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_share_3402_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_maxFVar_3403_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_proofInstInfo_3404_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_proofInstInfoFVar_3405_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_inferType_3406_);
lean_ctor_set(v_reuseFailAlloc_3431_, 5, v_getLevel_3407_);
lean_ctor_set(v_reuseFailAlloc_3431_, 6, v_congrInfo_3408_);
lean_ctor_set(v_reuseFailAlloc_3431_, 7, v_defEqI_3409_);
lean_ctor_set(v_reuseFailAlloc_3431_, 8, v_extensions_3410_);
lean_ctor_set(v_reuseFailAlloc_3431_, 9, v_issues_3411_);
lean_ctor_set(v_reuseFailAlloc_3431_, 10, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3431_, 11, v_instanceOverrides_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3431_, sizeof(void*)*12, v_debug_3413_);
v___x_3426_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_st_ref_put(v_a_3110_, v___x_3426_);
if (v_isShared_3399_ == 0)
{
v___x_3429_ = v___x_3398_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3396_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 4);
return v___x_3395_;
}
}
}
}
case 5:
{
if (v_a_3108_ == 0)
{
lean_object* v___x_3436_; lean_object* v_canon_3437_; lean_object* v_cache_3438_; lean_object* v___x_3439_; 
v___x_3436_ = lean_st_ref_get(v_a_3110_);
v_canon_3437_ = lean_ctor_get(v___x_3436_, 10);
lean_inc_ref(v_canon_3437_);
lean_dec(v___x_3436_);
v_cache_3438_ = lean_ctor_get(v_canon_3437_, 0);
lean_inc_ref(v_cache_3438_);
lean_dec_ref(v_canon_3437_);
v___x_3439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3438_, v_e_3107_);
lean_dec_ref(v_cache_3438_);
if (lean_obj_tag(v___x_3439_) == 1)
{
lean_object* v_val_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref_known(v_e_3107_, 2);
v_val_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_val_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 0);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_val_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
lean_object* v___x_3448_; 
lean_dec(v___x_3439_);
lean_inc_ref(v_e_3107_);
v___x_3448_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3488_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3488_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3488_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v_canon_3454_; lean_object* v_share_3455_; lean_object* v_maxFVar_3456_; lean_object* v_proofInstInfo_3457_; lean_object* v_proofInstInfoFVar_3458_; lean_object* v_inferType_3459_; lean_object* v_getLevel_3460_; lean_object* v_congrInfo_3461_; lean_object* v_defEqI_3462_; lean_object* v_extensions_3463_; lean_object* v_issues_3464_; lean_object* v_instanceOverrides_3465_; uint8_t v_debug_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3487_; 
v___x_3453_ = lean_st_ref_take(v_a_3110_);
v_canon_3454_ = lean_ctor_get(v___x_3453_, 10);
v_share_3455_ = lean_ctor_get(v___x_3453_, 0);
v_maxFVar_3456_ = lean_ctor_get(v___x_3453_, 1);
v_proofInstInfo_3457_ = lean_ctor_get(v___x_3453_, 2);
v_proofInstInfoFVar_3458_ = lean_ctor_get(v___x_3453_, 3);
v_inferType_3459_ = lean_ctor_get(v___x_3453_, 4);
v_getLevel_3460_ = lean_ctor_get(v___x_3453_, 5);
v_congrInfo_3461_ = lean_ctor_get(v___x_3453_, 6);
v_defEqI_3462_ = lean_ctor_get(v___x_3453_, 7);
v_extensions_3463_ = lean_ctor_get(v___x_3453_, 8);
v_issues_3464_ = lean_ctor_get(v___x_3453_, 9);
v_instanceOverrides_3465_ = lean_ctor_get(v___x_3453_, 11);
v_debug_3466_ = lean_ctor_get_uint8(v___x_3453_, sizeof(void*)*12);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3468_ = v___x_3453_;
v_isShared_3469_ = v_isSharedCheck_3487_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_instanceOverrides_3465_);
lean_inc(v_canon_3454_);
lean_inc(v_issues_3464_);
lean_inc(v_extensions_3463_);
lean_inc(v_defEqI_3462_);
lean_inc(v_congrInfo_3461_);
lean_inc(v_getLevel_3460_);
lean_inc(v_inferType_3459_);
lean_inc(v_proofInstInfoFVar_3458_);
lean_inc(v_proofInstInfo_3457_);
lean_inc(v_maxFVar_3456_);
lean_inc(v_share_3455_);
lean_dec(v___x_3453_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3487_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_cache_3470_; lean_object* v_cacheInType_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3486_; 
v_cache_3470_ = lean_ctor_get(v_canon_3454_, 0);
v_cacheInType_3471_ = lean_ctor_get(v_canon_3454_, 1);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_canon_3454_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3473_ = v_canon_3454_;
v_isShared_3474_ = v_isSharedCheck_3486_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_cacheInType_3471_);
lean_inc(v_cache_3470_);
lean_dec(v_canon_3454_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3486_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_inc(v_a_3449_);
v___x_3475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3470_, v_e_3107_, v_a_3449_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_cacheInType_3471_);
v___x_3477_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 10, v___x_3477_);
v___x_3479_ = v___x_3468_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_share_3455_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_maxFVar_3456_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_proofInstInfo_3457_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_proofInstInfoFVar_3458_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_inferType_3459_);
lean_ctor_set(v_reuseFailAlloc_3484_, 5, v_getLevel_3460_);
lean_ctor_set(v_reuseFailAlloc_3484_, 6, v_congrInfo_3461_);
lean_ctor_set(v_reuseFailAlloc_3484_, 7, v_defEqI_3462_);
lean_ctor_set(v_reuseFailAlloc_3484_, 8, v_extensions_3463_);
lean_ctor_set(v_reuseFailAlloc_3484_, 9, v_issues_3464_);
lean_ctor_set(v_reuseFailAlloc_3484_, 10, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3484_, 11, v_instanceOverrides_3465_);
lean_ctor_set_uint8(v_reuseFailAlloc_3484_, sizeof(void*)*12, v_debug_3466_);
v___x_3479_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = lean_st_ref_put(v_a_3110_, v___x_3479_);
if (v_isShared_3452_ == 0)
{
v___x_3482_ = v___x_3451_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3449_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 2);
return v___x_3448_;
}
}
}
else
{
lean_object* v___x_3489_; lean_object* v_canon_3490_; lean_object* v_cacheInType_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_st_ref_get(v_a_3110_);
v_canon_3490_ = lean_ctor_get(v___x_3489_, 10);
lean_inc_ref(v_canon_3490_);
lean_dec(v___x_3489_);
v_cacheInType_3491_ = lean_ctor_get(v_canon_3490_, 1);
lean_inc_ref(v_cacheInType_3491_);
lean_dec_ref(v_canon_3490_);
v___x_3492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3491_, v_e_3107_);
lean_dec_ref(v_cacheInType_3491_);
if (lean_obj_tag(v___x_3492_) == 1)
{
lean_object* v_val_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref_known(v_e_3107_, 2);
v_val_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_val_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 0);
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_val_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_object* v___x_3501_; 
lean_dec(v___x_3492_);
lean_inc_ref(v_e_3107_);
v___x_3501_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3541_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3541_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3541_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v_canon_3507_; lean_object* v_share_3508_; lean_object* v_maxFVar_3509_; lean_object* v_proofInstInfo_3510_; lean_object* v_proofInstInfoFVar_3511_; lean_object* v_inferType_3512_; lean_object* v_getLevel_3513_; lean_object* v_congrInfo_3514_; lean_object* v_defEqI_3515_; lean_object* v_extensions_3516_; lean_object* v_issues_3517_; lean_object* v_instanceOverrides_3518_; uint8_t v_debug_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3540_; 
v___x_3506_ = lean_st_ref_take(v_a_3110_);
v_canon_3507_ = lean_ctor_get(v___x_3506_, 10);
v_share_3508_ = lean_ctor_get(v___x_3506_, 0);
v_maxFVar_3509_ = lean_ctor_get(v___x_3506_, 1);
v_proofInstInfo_3510_ = lean_ctor_get(v___x_3506_, 2);
v_proofInstInfoFVar_3511_ = lean_ctor_get(v___x_3506_, 3);
v_inferType_3512_ = lean_ctor_get(v___x_3506_, 4);
v_getLevel_3513_ = lean_ctor_get(v___x_3506_, 5);
v_congrInfo_3514_ = lean_ctor_get(v___x_3506_, 6);
v_defEqI_3515_ = lean_ctor_get(v___x_3506_, 7);
v_extensions_3516_ = lean_ctor_get(v___x_3506_, 8);
v_issues_3517_ = lean_ctor_get(v___x_3506_, 9);
v_instanceOverrides_3518_ = lean_ctor_get(v___x_3506_, 11);
v_debug_3519_ = lean_ctor_get_uint8(v___x_3506_, sizeof(void*)*12);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3521_ = v___x_3506_;
v_isShared_3522_ = v_isSharedCheck_3540_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_instanceOverrides_3518_);
lean_inc(v_canon_3507_);
lean_inc(v_issues_3517_);
lean_inc(v_extensions_3516_);
lean_inc(v_defEqI_3515_);
lean_inc(v_congrInfo_3514_);
lean_inc(v_getLevel_3513_);
lean_inc(v_inferType_3512_);
lean_inc(v_proofInstInfoFVar_3511_);
lean_inc(v_proofInstInfo_3510_);
lean_inc(v_maxFVar_3509_);
lean_inc(v_share_3508_);
lean_dec(v___x_3506_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3540_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_cache_3523_; lean_object* v_cacheInType_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3539_; 
v_cache_3523_ = lean_ctor_get(v_canon_3507_, 0);
v_cacheInType_3524_ = lean_ctor_get(v_canon_3507_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_canon_3507_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3526_ = v_canon_3507_;
v_isShared_3527_ = v_isSharedCheck_3539_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_cacheInType_3524_);
lean_inc(v_cache_3523_);
lean_dec(v_canon_3507_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3539_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_inc(v_a_3502_);
v___x_3528_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3524_, v_e_3107_, v_a_3502_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v___x_3528_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_cache_3523_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 10, v___x_3530_);
v___x_3532_ = v___x_3521_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_share_3508_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_maxFVar_3509_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_proofInstInfo_3510_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_proofInstInfoFVar_3511_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_inferType_3512_);
lean_ctor_set(v_reuseFailAlloc_3537_, 5, v_getLevel_3513_);
lean_ctor_set(v_reuseFailAlloc_3537_, 6, v_congrInfo_3514_);
lean_ctor_set(v_reuseFailAlloc_3537_, 7, v_defEqI_3515_);
lean_ctor_set(v_reuseFailAlloc_3537_, 8, v_extensions_3516_);
lean_ctor_set(v_reuseFailAlloc_3537_, 9, v_issues_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 10, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3537_, 11, v_instanceOverrides_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*12, v_debug_3519_);
v___x_3532_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_st_ref_put(v_a_3110_, v___x_3532_);
if (v_isShared_3505_ == 0)
{
v___x_3535_ = v___x_3504_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3502_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 2);
return v___x_3501_;
}
}
}
}
case 11:
{
if (v_a_3108_ == 0)
{
lean_object* v___x_3542_; lean_object* v_canon_3543_; lean_object* v_cache_3544_; lean_object* v___x_3545_; 
v___x_3542_ = lean_st_ref_get(v_a_3110_);
v_canon_3543_ = lean_ctor_get(v___x_3542_, 10);
lean_inc_ref(v_canon_3543_);
lean_dec(v___x_3542_);
v_cache_3544_ = lean_ctor_get(v_canon_3543_, 0);
lean_inc_ref(v_cache_3544_);
lean_dec_ref(v_canon_3543_);
v___x_3545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3544_, v_e_3107_);
lean_dec_ref(v_cache_3544_);
if (lean_obj_tag(v___x_3545_) == 1)
{
lean_object* v_val_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_val_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set_tag(v___x_3548_, 0);
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_val_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
else
{
lean_object* v___x_3554_; 
lean_dec(v___x_3545_);
lean_inc_ref(v_e_3107_);
v___x_3554_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3594_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3594_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3594_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v_canon_3560_; lean_object* v_share_3561_; lean_object* v_maxFVar_3562_; lean_object* v_proofInstInfo_3563_; lean_object* v_proofInstInfoFVar_3564_; lean_object* v_inferType_3565_; lean_object* v_getLevel_3566_; lean_object* v_congrInfo_3567_; lean_object* v_defEqI_3568_; lean_object* v_extensions_3569_; lean_object* v_issues_3570_; lean_object* v_instanceOverrides_3571_; uint8_t v_debug_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3593_; 
v___x_3559_ = lean_st_ref_take(v_a_3110_);
v_canon_3560_ = lean_ctor_get(v___x_3559_, 10);
v_share_3561_ = lean_ctor_get(v___x_3559_, 0);
v_maxFVar_3562_ = lean_ctor_get(v___x_3559_, 1);
v_proofInstInfo_3563_ = lean_ctor_get(v___x_3559_, 2);
v_proofInstInfoFVar_3564_ = lean_ctor_get(v___x_3559_, 3);
v_inferType_3565_ = lean_ctor_get(v___x_3559_, 4);
v_getLevel_3566_ = lean_ctor_get(v___x_3559_, 5);
v_congrInfo_3567_ = lean_ctor_get(v___x_3559_, 6);
v_defEqI_3568_ = lean_ctor_get(v___x_3559_, 7);
v_extensions_3569_ = lean_ctor_get(v___x_3559_, 8);
v_issues_3570_ = lean_ctor_get(v___x_3559_, 9);
v_instanceOverrides_3571_ = lean_ctor_get(v___x_3559_, 11);
v_debug_3572_ = lean_ctor_get_uint8(v___x_3559_, sizeof(void*)*12);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3574_ = v___x_3559_;
v_isShared_3575_ = v_isSharedCheck_3593_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_instanceOverrides_3571_);
lean_inc(v_canon_3560_);
lean_inc(v_issues_3570_);
lean_inc(v_extensions_3569_);
lean_inc(v_defEqI_3568_);
lean_inc(v_congrInfo_3567_);
lean_inc(v_getLevel_3566_);
lean_inc(v_inferType_3565_);
lean_inc(v_proofInstInfoFVar_3564_);
lean_inc(v_proofInstInfo_3563_);
lean_inc(v_maxFVar_3562_);
lean_inc(v_share_3561_);
lean_dec(v___x_3559_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3593_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_cache_3576_; lean_object* v_cacheInType_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3592_; 
v_cache_3576_ = lean_ctor_get(v_canon_3560_, 0);
v_cacheInType_3577_ = lean_ctor_get(v_canon_3560_, 1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_canon_3560_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3579_ = v_canon_3560_;
v_isShared_3580_ = v_isSharedCheck_3592_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_cacheInType_3577_);
lean_inc(v_cache_3576_);
lean_dec(v_canon_3560_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3592_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_inc(v_a_3555_);
v___x_3581_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3576_, v_e_3107_, v_a_3555_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3581_);
v___x_3583_ = v___x_3579_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_cacheInType_3577_);
v___x_3583_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 10, v___x_3583_);
v___x_3585_ = v___x_3574_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_share_3561_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_maxFVar_3562_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_proofInstInfo_3563_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_proofInstInfoFVar_3564_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_inferType_3565_);
lean_ctor_set(v_reuseFailAlloc_3590_, 5, v_getLevel_3566_);
lean_ctor_set(v_reuseFailAlloc_3590_, 6, v_congrInfo_3567_);
lean_ctor_set(v_reuseFailAlloc_3590_, 7, v_defEqI_3568_);
lean_ctor_set(v_reuseFailAlloc_3590_, 8, v_extensions_3569_);
lean_ctor_set(v_reuseFailAlloc_3590_, 9, v_issues_3570_);
lean_ctor_set(v_reuseFailAlloc_3590_, 10, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3590_, 11, v_instanceOverrides_3571_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*12, v_debug_3572_);
v___x_3585_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_st_ref_put(v_a_3110_, v___x_3585_);
if (v_isShared_3558_ == 0)
{
v___x_3588_ = v___x_3557_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3555_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3554_;
}
}
}
else
{
lean_object* v___x_3595_; lean_object* v_canon_3596_; lean_object* v_cacheInType_3597_; lean_object* v___x_3598_; 
v___x_3595_ = lean_st_ref_get(v_a_3110_);
v_canon_3596_ = lean_ctor_get(v___x_3595_, 10);
lean_inc_ref(v_canon_3596_);
lean_dec(v___x_3595_);
v_cacheInType_3597_ = lean_ctor_get(v_canon_3596_, 1);
lean_inc_ref(v_cacheInType_3597_);
lean_dec_ref(v_canon_3596_);
v___x_3598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3597_, v_e_3107_);
lean_dec_ref(v_cacheInType_3597_);
if (lean_obj_tag(v___x_3598_) == 1)
{
lean_object* v_val_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref_known(v_e_3107_, 3);
v_val_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_val_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 0);
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_val_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v___x_3598_);
lean_inc_ref(v_e_3107_);
v___x_3607_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3647_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v_canon_3613_; lean_object* v_share_3614_; lean_object* v_maxFVar_3615_; lean_object* v_proofInstInfo_3616_; lean_object* v_proofInstInfoFVar_3617_; lean_object* v_inferType_3618_; lean_object* v_getLevel_3619_; lean_object* v_congrInfo_3620_; lean_object* v_defEqI_3621_; lean_object* v_extensions_3622_; lean_object* v_issues_3623_; lean_object* v_instanceOverrides_3624_; uint8_t v_debug_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3646_; 
v___x_3612_ = lean_st_ref_take(v_a_3110_);
v_canon_3613_ = lean_ctor_get(v___x_3612_, 10);
v_share_3614_ = lean_ctor_get(v___x_3612_, 0);
v_maxFVar_3615_ = lean_ctor_get(v___x_3612_, 1);
v_proofInstInfo_3616_ = lean_ctor_get(v___x_3612_, 2);
v_proofInstInfoFVar_3617_ = lean_ctor_get(v___x_3612_, 3);
v_inferType_3618_ = lean_ctor_get(v___x_3612_, 4);
v_getLevel_3619_ = lean_ctor_get(v___x_3612_, 5);
v_congrInfo_3620_ = lean_ctor_get(v___x_3612_, 6);
v_defEqI_3621_ = lean_ctor_get(v___x_3612_, 7);
v_extensions_3622_ = lean_ctor_get(v___x_3612_, 8);
v_issues_3623_ = lean_ctor_get(v___x_3612_, 9);
v_instanceOverrides_3624_ = lean_ctor_get(v___x_3612_, 11);
v_debug_3625_ = lean_ctor_get_uint8(v___x_3612_, sizeof(void*)*12);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3627_ = v___x_3612_;
v_isShared_3628_ = v_isSharedCheck_3646_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_instanceOverrides_3624_);
lean_inc(v_canon_3613_);
lean_inc(v_issues_3623_);
lean_inc(v_extensions_3622_);
lean_inc(v_defEqI_3621_);
lean_inc(v_congrInfo_3620_);
lean_inc(v_getLevel_3619_);
lean_inc(v_inferType_3618_);
lean_inc(v_proofInstInfoFVar_3617_);
lean_inc(v_proofInstInfo_3616_);
lean_inc(v_maxFVar_3615_);
lean_inc(v_share_3614_);
lean_dec(v___x_3612_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3646_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_cache_3629_; lean_object* v_cacheInType_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3645_; 
v_cache_3629_ = lean_ctor_get(v_canon_3613_, 0);
v_cacheInType_3630_ = lean_ctor_get(v_canon_3613_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_canon_3613_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3632_ = v_canon_3613_;
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_cacheInType_3630_);
lean_inc(v_cache_3629_);
lean_dec(v_canon_3613_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_inc(v_a_3608_);
v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3630_, v_e_3107_, v_a_3608_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 1, v___x_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_cache_3629_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 10, v___x_3636_);
v___x_3638_ = v___x_3627_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_share_3614_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_maxFVar_3615_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_proofInstInfo_3616_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_proofInstInfoFVar_3617_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_inferType_3618_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_getLevel_3619_);
lean_ctor_set(v_reuseFailAlloc_3643_, 6, v_congrInfo_3620_);
lean_ctor_set(v_reuseFailAlloc_3643_, 7, v_defEqI_3621_);
lean_ctor_set(v_reuseFailAlloc_3643_, 8, v_extensions_3622_);
lean_ctor_set(v_reuseFailAlloc_3643_, 9, v_issues_3623_);
lean_ctor_set(v_reuseFailAlloc_3643_, 10, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3643_, 11, v_instanceOverrides_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*12, v_debug_3625_);
v___x_3638_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_st_ref_put(v_a_3110_, v___x_3638_);
if (v_isShared_3611_ == 0)
{
v___x_3641_ = v___x_3610_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3608_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 3);
return v___x_3607_;
}
}
}
}
case 10:
{
lean_object* v_data_3648_; lean_object* v_expr_3649_; lean_object* v___x_3650_; 
v_data_3648_ = lean_ctor_get(v_e_3107_, 0);
v_expr_3649_ = lean_ctor_get(v_e_3107_, 1);
lean_inc_ref(v_expr_3649_);
v___x_3650_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3649_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3665_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
size_t v___x_3655_; size_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = lean_ptr_addr(v_expr_3649_);
v___x_3656_ = lean_ptr_addr(v_a_3651_);
v___x_3657_ = lean_usize_dec_eq(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_inc(v_data_3648_);
lean_dec_ref_known(v_e_3107_, 2);
v___x_3658_ = l_Lean_Expr_mdata___override(v_data_3648_, v_a_3651_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3658_);
v___x_3660_ = v___x_3653_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
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
lean_dec(v_a_3651_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v_e_3107_);
v___x_3663_ = v___x_3653_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_e_3107_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3107_, 2);
return v___x_3650_;
}
}
default: 
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v_e_3107_);
return v___x_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3667_, uint8_t v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
if (v_a_3668_ == 0)
{
uint8_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = 1;
lean_inc_ref(v_e_3667_);
v___x_3677_ = l_Lean_Meta_isProp(v_e_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; uint8_t v___x_3679_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = lean_unbox(v_a_3678_);
lean_dec(v_a_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
v___x_3680_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3667_, v___x_3676_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3680_;
}
else
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3681_;
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v_e_3667_);
v_a_3682_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3677_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3677_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3691_, lean_object* v_e_3692_, uint8_t v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
if (lean_obj_tag(v_e_3692_) == 7)
{
lean_object* v_binderName_3701_; lean_object* v_binderType_3702_; lean_object* v_body_3703_; uint8_t v_binderInfo_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_binderName_3701_ = lean_ctor_get(v_e_3692_, 0);
lean_inc(v_binderName_3701_);
v_binderType_3702_ = lean_ctor_get(v_e_3692_, 1);
lean_inc_ref(v_binderType_3702_);
v_body_3703_ = lean_ctor_get(v_e_3692_, 2);
lean_inc_ref(v_body_3703_);
v_binderInfo_3704_ = lean_ctor_get_uint8(v_e_3692_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3692_, 3);
lean_inc_ref(v_fvars_3691_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3705_, 0, v_fvars_3691_);
lean_closure_set(v___f_3705_, 1, v_body_3703_);
v___x_3706_ = lean_expr_instantiate_rev(v_binderType_3702_, v_fvars_3691_);
lean_dec_ref(v_fvars_3691_);
lean_dec_ref(v_binderType_3702_);
v___x_3707_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3706_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(v_binderName_3701_, v_binderInfo_3704_, v_a_3708_, v___f_3705_, v___x_3709_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
return v___x_3710_;
}
else
{
lean_dec_ref(v___f_3705_);
lean_dec(v_binderName_3701_);
return v___x_3707_;
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_expr_instantiate_rev(v_e_3692_, v_fvars_3691_);
lean_dec_ref(v_e_3692_);
v___x_3712_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3711_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; uint8_t v___x_3714_; uint8_t v___x_3715_; uint8_t v___x_3716_; lean_object* v___x_3717_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = 0;
v___x_3715_ = 1;
v___x_3716_ = 1;
v___x_3717_ = l_Lean_Meta_mkForallFVars(v_fvars_3691_, v_a_3713_, v___x_3714_, v___x_3715_, v___x_3715_, v___x_3716_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec_ref(v_fvars_3691_);
return v___x_3717_;
}
else
{
lean_dec_ref(v_fvars_3691_);
return v___x_3712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3718_, lean_object* v_body_3719_, lean_object* v_x_3720_, uint8_t v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_array_push(v_fvars_3718_, v_x_3720_);
v___x_3730_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3729_, v_body_3719_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
uint8_t v_a_boxed_3740_; lean_object* v_res_3741_; 
v_a_boxed_3740_ = lean_unbox(v_a_3732_);
v_res_3741_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3731_, v_a_boxed_3740_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
uint8_t v_a_boxed_3751_; lean_object* v_res_3752_; 
v_a_boxed_3751_ = lean_unbox(v_a_3743_);
v_res_3752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3742_, v_a_boxed_3751_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
uint8_t v_a_boxed_3762_; lean_object* v_res_3763_; 
v_a_boxed_3762_ = lean_unbox(v_a_3754_);
v_res_3763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3753_, v_a_boxed_3762_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_){
_start:
{
uint8_t v_a_boxed_3773_; lean_object* v_res_3774_; 
v_a_boxed_3773_ = lean_unbox(v_a_3765_);
v_res_3774_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3764_, v_a_boxed_3773_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
uint8_t v_a_boxed_3784_; lean_object* v_res_3785_; 
v_a_boxed_3784_ = lean_unbox(v_a_3776_);
v_res_3785_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3775_, v_a_boxed_3784_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3786_, lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
uint8_t v_a_boxed_3796_; lean_object* v_res_3797_; 
v_a_boxed_3796_ = lean_unbox(v_a_3788_);
v_res_3797_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3786_, v_e_3787_, v_a_boxed_3796_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3798_, lean_object* v_e_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
uint8_t v_a_boxed_3808_; lean_object* v_res_3809_; 
v_a_boxed_3808_ = lean_unbox(v_a_3800_);
v_res_3809_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3798_, v_e_3799_, v_a_boxed_3808_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3810_, lean_object* v_report_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
uint8_t v_report_boxed_3820_; uint8_t v_a_boxed_3821_; lean_object* v_res_3822_; 
v_report_boxed_3820_ = lean_unbox(v_report_3811_);
v_a_boxed_3821_ = lean_unbox(v_a_3812_);
v_res_3822_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3810_, v_report_boxed_3820_, v_a_boxed_3821_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
uint8_t v_a_boxed_3832_; lean_object* v_res_3833_; 
v_a_boxed_3832_ = lean_unbox(v_a_3824_);
v_res_3833_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3823_, v_a_boxed_3832_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3834_, lean_object* v_e_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
uint8_t v_a_boxed_3844_; lean_object* v_res_3845_; 
v_a_boxed_3844_ = lean_unbox(v_a_3836_);
v_res_3845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3834_, v_e_3835_, v_a_boxed_3844_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3846_, lean_object* v_00_u03b1_3847_, lean_object* v_c_3848_, lean_object* v_a_3849_, lean_object* v_b_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
uint8_t v_a_boxed_3859_; lean_object* v_res_3860_; 
v_a_boxed_3859_ = lean_unbox(v_a_3851_);
v_res_3860_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3846_, v_00_u03b1_3847_, v_c_3848_, v_a_3849_, v_b_3850_, v_a_boxed_3859_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3861_, lean_object* v_00_u03b1_3862_, lean_object* v_c_3863_, lean_object* v_inst_3864_, lean_object* v_a_3865_, lean_object* v_b_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
uint8_t v_a_boxed_3875_; lean_object* v_res_3876_; 
v_a_boxed_3875_ = lean_unbox(v_a_3867_);
v_res_3876_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3861_, v_00_u03b1_3862_, v_c_3863_, v_inst_3864_, v_a_3865_, v_b_3866_, v_a_boxed_3875_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
uint8_t v_a_boxed_3886_; lean_object* v_res_3887_; 
v_a_boxed_3886_ = lean_unbox(v_a_3878_);
v_res_3887_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3877_, v_a_boxed_3886_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
uint8_t v_a_boxed_3897_; lean_object* v_res_3898_; 
v_a_boxed_3897_ = lean_unbox(v_a_3889_);
v_res_3898_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3888_, v_a_boxed_3897_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3899_, lean_object* v_prop_3900_, lean_object* v_inst_3901_, lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
uint8_t v_a_boxed_3911_; lean_object* v_res_3912_; 
v_a_boxed_3911_ = lean_unbox(v_a_3903_);
v_res_3912_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3899_, v_prop_3900_, v_inst_3901_, v_e_3902_, v_a_boxed_3911_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3913_, lean_object* v_report_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
uint8_t v_report_boxed_3923_; uint8_t v_a_boxed_3924_; lean_object* v_res_3925_; 
v_report_boxed_3923_ = lean_unbox(v_report_3914_);
v_a_boxed_3924_ = lean_unbox(v_a_3915_);
v_res_3925_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3913_, v_report_boxed_3923_, v_a_boxed_3924_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3926_, lean_object* v_prop_3927_, lean_object* v_h_3928_, lean_object* v_e_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
uint8_t v_a_boxed_3938_; lean_object* v_res_3939_; 
v_a_boxed_3938_ = lean_unbox(v_a_3930_);
v_res_3939_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3926_, v_prop_3927_, v_h_3928_, v_e_3929_, v_a_boxed_3938_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_3940_, lean_object* v_type_3941_, lean_object* v_report_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
uint8_t v_report_boxed_3951_; uint8_t v_a_boxed_3952_; lean_object* v_res_3953_; 
v_report_boxed_3951_ = lean_unbox(v_report_3942_);
v_a_boxed_3952_ = lean_unbox(v_a_3943_);
v_res_3953_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_3940_, v_type_3941_, v_report_boxed_3951_, v_a_boxed_3952_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
uint8_t v_a_boxed_3963_; lean_object* v_res_3964_; 
v_a_boxed_3963_ = lean_unbox(v_a_3955_);
v_res_3964_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3954_, v_a_boxed_3963_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3965_, lean_object* v___x_3966_, lean_object* v_a_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
uint8_t v___y_65325__boxed_3977_; lean_object* v_res_3978_; 
v___y_65325__boxed_3977_ = lean_unbox(v___y_3969_);
v_res_3978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3965_, v___x_3966_, v_a_3967_, v_b_3968_, v___y_65325__boxed_3977_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec_ref(v___x_3966_);
lean_dec(v_upperBound_3965_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_3979_, lean_object* v_snd_3980_, lean_object* v_a_3981_, lean_object* v___x_3982_, lean_object* v_fst_3983_, lean_object* v___x_3984_, lean_object* v_____r_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
uint8_t v___x_65389__boxed_3994_; uint8_t v___y_65392__boxed_3995_; lean_object* v_res_3996_; 
v___x_65389__boxed_3994_ = lean_unbox(v___x_3982_);
v___y_65392__boxed_3995_ = lean_unbox(v___y_3986_);
v_res_3996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_3979_, v_snd_3980_, v_a_3981_, v___x_65389__boxed_3994_, v_fst_3983_, v___x_3984_, v_____r_3985_, v___y_65392__boxed_3995_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___x_3984_);
lean_dec(v_a_3981_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3997_, lean_object* v_prop_3998_, lean_object* v_h_3999_, lean_object* v_e_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
uint8_t v_a_boxed_4009_; lean_object* v_res_4010_; 
v_a_boxed_4009_ = lean_unbox(v_a_4001_);
v_res_4010_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3997_, v_prop_3998_, v_h_3999_, v_e_4000_, v_a_boxed_4009_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
uint8_t v_a_boxed_4020_; lean_object* v_res_4021_; 
v_a_boxed_4020_ = lean_unbox(v_a_4012_);
v_res_4021_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_4011_, v_a_boxed_4020_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_, lean_object* v_x_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___y_65566__boxed_4034_; lean_object* v_res_4035_; 
v___y_65566__boxed_4034_ = lean_unbox(v___y_4026_);
v_res_4035_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_4022_, v_x_4023_, v_x_4024_, v_x_4025_, v___y_65566__boxed_4034_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
uint8_t v_a_boxed_4045_; lean_object* v_res_4046_; 
v_a_boxed_4045_ = lean_unbox(v_a_4037_);
v_res_4046_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4036_, v_a_boxed_4045_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_4047_, uint8_t v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_4047_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v___y_68211__boxed_4066_; lean_object* v_res_4067_; 
v___y_68211__boxed_4066_ = lean_unbox(v___y_4058_);
v_res_4067_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4057_, v___y_68211__boxed_4066_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_4068_, uint8_t v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_4068_, v___y_4075_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v___y_68237__boxed_4087_; lean_object* v_res_4088_; 
v___y_68237__boxed_4087_ = lean_unbox(v___y_4079_);
v_res_4088_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4078_, v___y_68237__boxed_4087_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26(lean_object* v_00_u03b1_4089_, lean_object* v_name_4090_, lean_object* v_type_4091_, lean_object* v_val_4092_, lean_object* v_k_4093_, uint8_t v_nondep_4094_, uint8_t v_kind_4095_, uint8_t v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___redArg(v_name_4090_, v_type_4091_, v_val_4092_, v_k_4093_, v_nondep_4094_, v_kind_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26___boxed(lean_object* v_00_u03b1_4105_, lean_object* v_name_4106_, lean_object* v_type_4107_, lean_object* v_val_4108_, lean_object* v_k_4109_, lean_object* v_nondep_4110_, lean_object* v_kind_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
uint8_t v_nondep_boxed_4120_; uint8_t v_kind_boxed_4121_; uint8_t v___y_68263__boxed_4122_; lean_object* v_res_4123_; 
v_nondep_boxed_4120_ = lean_unbox(v_nondep_4110_);
v_kind_boxed_4121_ = lean_unbox(v_kind_4111_);
v___y_68263__boxed_4122_ = lean_unbox(v___y_4112_);
v_res_4123_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__26(v_00_u03b1_4105_, v_name_4106_, v_type_4107_, v_val_4108_, v_k_4109_, v_nondep_boxed_4120_, v_kind_boxed_4121_, v___y_68263__boxed_4122_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29(lean_object* v_00_u03b1_4124_, lean_object* v_name_4125_, uint8_t v_bi_4126_, lean_object* v_type_4127_, lean_object* v_k_4128_, uint8_t v_kind_4129_, uint8_t v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___redArg(v_name_4125_, v_bi_4126_, v_type_4127_, v_k_4128_, v_kind_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29___boxed(lean_object* v_00_u03b1_4139_, lean_object* v_name_4140_, lean_object* v_bi_4141_, lean_object* v_type_4142_, lean_object* v_k_4143_, lean_object* v_kind_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
uint8_t v_bi_boxed_4153_; uint8_t v_kind_boxed_4154_; uint8_t v___y_68289__boxed_4155_; lean_object* v_res_4156_; 
v_bi_boxed_4153_ = lean_unbox(v_bi_4141_);
v_kind_boxed_4154_ = lean_unbox(v_kind_4144_);
v___y_68289__boxed_4155_ = lean_unbox(v___y_4145_);
v_res_4156_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__29(v_00_u03b1_4139_, v_name_4140_, v_bi_boxed_4153_, v_type_4142_, v_k_4143_, v_kind_boxed_4154_, v___y_68289__boxed_4155_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4157_, lean_object* v_m_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4158_, v_a_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4161_, lean_object* v_m_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4161_, v_m_4162_, v_a_4163_);
lean_dec_ref(v_a_4163_);
lean_dec_ref(v_m_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4165_, lean_object* v_m_4166_, lean_object* v_a_4167_, lean_object* v_b_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4166_, v_a_4167_, v_b_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4170_, lean_object* v_msg_4171_, uint8_t v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4170_, v_msg_4171_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4181_, lean_object* v_msg_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v___y_68319__boxed_4191_; lean_object* v_res_4192_; 
v___y_68319__boxed_4191_ = lean_unbox(v___y_4183_);
v_res_4192_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4181_, v_msg_4182_, v___y_68319__boxed_4191_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4193_, lean_object* v___x_4194_, lean_object* v___x_4195_, lean_object* v_inst_4196_, lean_object* v_R_4197_, lean_object* v_a_4198_, lean_object* v_b_4199_, lean_object* v_c_4200_, uint8_t v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4193_, v___x_4195_, v_a_4198_, v_b_4199_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v_inst_4213_, lean_object* v_R_4214_, lean_object* v_a_4215_, lean_object* v_b_4216_, lean_object* v_c_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___y_68349__boxed_4226_; lean_object* v_res_4227_; 
v___y_68349__boxed_4226_ = lean_unbox(v___y_4218_);
v_res_4227_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4210_, v___x_4211_, v___x_4212_, v_inst_4213_, v_R_4214_, v_a_4215_, v_b_4216_, v_c_4217_, v___y_68349__boxed_4226_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v_upperBound_4210_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4228_, lean_object* v_a_4229_, lean_object* v_x_4230_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4229_, v_x_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4232_, lean_object* v_a_4233_, lean_object* v_x_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4232_, v_a_4233_, v_x_4234_);
lean_dec(v_x_4234_);
lean_dec_ref(v_a_4233_);
return v_res_4235_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4236_, lean_object* v_a_4237_, lean_object* v_x_4238_){
_start:
{
uint8_t v___x_4239_; 
v___x_4239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4237_, v_x_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4240_, lean_object* v_a_4241_, lean_object* v_x_4242_){
_start:
{
uint8_t v_res_4243_; lean_object* v_r_4244_; 
v_res_4243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4240_, v_a_4241_, v_x_4242_);
lean_dec(v_x_4242_);
lean_dec_ref(v_a_4241_);
v_r_4244_ = lean_box(v_res_4243_);
return v_r_4244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4245_, lean_object* v_data_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4248_, lean_object* v_a_4249_, lean_object* v_b_4250_, lean_object* v_x_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4249_, v_b_4250_, v_x_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30(lean_object* v_00_u03b2_4253_, lean_object* v_i_4254_, lean_object* v_source_4255_, lean_object* v_target_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30___redArg(v_i_4254_, v_source_4255_, v_target_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35(lean_object* v_00_u03b2_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__30_spec__35___redArg(v_x_4259_, v_x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4262_, lean_object* v_i_4263_, lean_object* v_arg_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4262_, v_i_4263_, v_arg_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4286_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4286_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4286_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_unbox(v_a_4271_);
lean_dec(v_a_4271_);
if (v___x_4275_ == 3)
{
uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; 
v___x_4276_ = 0;
v___x_4277_ = lean_box(v___x_4276_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4277_);
v___x_4279_ = v___x_4273_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
else
{
uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4281_ = 1;
v___x_4282_ = lean_box(v___x_4281_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4282_);
v___x_4284_ = v___x_4273_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
v_a_4287_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4270_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4270_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4295_, lean_object* v_i_4296_, lean_object* v_arg_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4295_, v_i_4296_, v_arg_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_i_4296_);
lean_dec_ref(v_pinfos_4295_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4304_, lean_object* v_opts_4305_, lean_object* v_act_4306_, lean_object* v_decl_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4309_);
lean_inc_ref(v___y_4308_);
v___x_4315_ = lean_apply_6(v_act_4306_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
v___x_4316_ = l_Lean_profileitIOUnsafe___redArg(v_category_4304_, v_opts_4305_, v___x_4315_, v_decl_4307_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4317_, lean_object* v_opts_4318_, lean_object* v_act_4319_, lean_object* v_decl_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4317_, v_opts_4318_, v_act_4319_, v_decl_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec_ref(v_opts_4318_);
lean_dec_ref(v_category_4317_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4329_, lean_object* v_category_4330_, lean_object* v_opts_4331_, lean_object* v_act_4332_, lean_object* v_decl_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4330_, v_opts_4331_, v_act_4332_, v_decl_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4342_, lean_object* v_category_4343_, lean_object* v_opts_4344_, lean_object* v_act_4345_, lean_object* v_decl_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4342_, v_category_4343_, v_opts_4344_, v_act_4345_, v_decl_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec_ref(v_opts_4344_);
lean_dec_ref(v_category_4343_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4355_, lean_object* v_e_4356_, uint8_t v___x_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___y_4366_; lean_object* v___x_4375_; uint8_t v_transparency_4376_; uint8_t v___x_4377_; 
v___x_4375_ = l_Lean_Meta_Context_config(v___y_4360_);
v_transparency_4376_ = lean_ctor_get_uint8(v___x_4375_, 9);
lean_dec_ref(v___x_4375_);
v___x_4377_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4376_, v___x_4355_);
if (v___x_4377_ == 0)
{
lean_object* v_keyedConfig_4378_; uint8_t v_trackZetaDelta_4379_; lean_object* v_zetaDeltaSet_4380_; lean_object* v_lctx_4381_; lean_object* v_localInstances_4382_; lean_object* v_defEqCtx_x3f_4383_; lean_object* v_synthPendingDepth_4384_; lean_object* v_customCanUnfoldPredicate_x3f_4385_; uint8_t v_univApprox_4386_; uint8_t v_inTypeClassResolution_4387_; uint8_t v_cacheInferType_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_keyedConfig_4378_ = lean_ctor_get(v___y_4360_, 0);
v_trackZetaDelta_4379_ = lean_ctor_get_uint8(v___y_4360_, sizeof(void*)*7);
v_zetaDeltaSet_4380_ = lean_ctor_get(v___y_4360_, 1);
v_lctx_4381_ = lean_ctor_get(v___y_4360_, 2);
v_localInstances_4382_ = lean_ctor_get(v___y_4360_, 3);
v_defEqCtx_x3f_4383_ = lean_ctor_get(v___y_4360_, 4);
v_synthPendingDepth_4384_ = lean_ctor_get(v___y_4360_, 5);
v_customCanUnfoldPredicate_x3f_4385_ = lean_ctor_get(v___y_4360_, 6);
v_univApprox_4386_ = lean_ctor_get_uint8(v___y_4360_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4387_ = lean_ctor_get_uint8(v___y_4360_, sizeof(void*)*7 + 2);
v_cacheInferType_4388_ = lean_ctor_get_uint8(v___y_4360_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4378_);
v___x_4389_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4355_, v_keyedConfig_4378_);
lean_inc(v_customCanUnfoldPredicate_x3f_4385_);
lean_inc(v_synthPendingDepth_4384_);
lean_inc(v_defEqCtx_x3f_4383_);
lean_inc_ref(v_localInstances_4382_);
lean_inc_ref(v_lctx_4381_);
lean_inc(v_zetaDeltaSet_4380_);
v___x_4390_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v_zetaDeltaSet_4380_);
lean_ctor_set(v___x_4390_, 2, v_lctx_4381_);
lean_ctor_set(v___x_4390_, 3, v_localInstances_4382_);
lean_ctor_set(v___x_4390_, 4, v_defEqCtx_x3f_4383_);
lean_ctor_set(v___x_4390_, 5, v_synthPendingDepth_4384_);
lean_ctor_set(v___x_4390_, 6, v_customCanUnfoldPredicate_x3f_4385_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*7, v_trackZetaDelta_4379_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*7 + 1, v_univApprox_4386_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4387_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*7 + 3, v_cacheInferType_4388_);
v___x_4391_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4356_, v___x_4357_, v___y_4358_, v___y_4359_, v___x_4390_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec_ref_known(v___x_4390_, 7);
v___y_4366_ = v___x_4391_;
goto v___jp_4365_;
}
else
{
lean_object* v___x_4392_; 
v___x_4392_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4356_, v___x_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
v___y_4366_ = v___x_4392_;
goto v___jp_4365_;
}
v___jp_4365_:
{
if (lean_obj_tag(v___y_4366_) == 0)
{
return v___y_4366_;
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_a_4367_ = lean_ctor_get(v___y_4366_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___y_4366_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___y_4366_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___y_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4393_, lean_object* v_e_4394_, lean_object* v___x_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
uint8_t v___x_2117__boxed_4403_; uint8_t v___x_2118__boxed_4404_; lean_object* v_res_4405_; 
v___x_2117__boxed_4403_ = lean_unbox(v___x_4393_);
v___x_2118__boxed_4404_ = lean_unbox(v___x_4395_);
v_res_4405_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2117__boxed_4403_, v_e_4394_, v___x_2118__boxed_4404_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; uint8_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___f_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4415_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4412_);
v___x_4416_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4417_ = 0;
v___x_4418_ = 2;
v___x_4419_ = lean_box(v___x_4418_);
v___x_4420_ = lean_box(v___x_4417_);
v___f_4421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4421_, 0, v___x_4419_);
lean_closure_set(v___f_4421_, 1, v_e_4407_);
lean_closure_set(v___f_4421_, 2, v___x_4420_);
v___x_4422_ = lean_box(0);
v___x_4423_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4416_, v___x_4415_, v___f_4421_, v___x_4422_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec_ref(v___x_4415_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_Meta_Sym_canon(v_e_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
return v_res_4432_;
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

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
uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_110_; uint8_t v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v_modified_172_; 
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_110_, v___y_112_);
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
v___y_105_ = v___y_111_;
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
v___y_110_ = v_inst_144_;
v___y_111_ = v_modified_141_;
v___y_112_ = v___y_142_;
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
v___y_110_ = v_inst_144_;
v___y_111_ = v_modified_141_;
v___y_112_ = v___y_142_;
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
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_506_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_506_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_506_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_506_;
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
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_304_);
v___x_466_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_466_;
}
}
}
else
{
uint8_t v___x_467_; 
lean_dec_ref(v___x_305_);
v___x_467_ = l_Lean_Expr_isCharLit(v_e_288_);
lean_dec_ref(v_e_288_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_del_object(v___x_300_);
v___x_468_ = l_Lean_Meta_getNatValue_x3f(v_arg_304_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_arg_304_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_493_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_493_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_488_; 
v_val_473_ = lean_ctor_get(v_a_469_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_488_ == 0)
{
v___x_475_ = v_a_469_;
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_val_473_);
lean_dec(v_a_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint32_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_477_ = l_Char_ofNat(v_val_473_);
lean_dec(v_val_473_);
v___x_478_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9);
v___x_479_ = lean_uint32_to_nat(v___x_477_);
v___x_480_ = l_Lean_mkRawNatLit(v___x_479_);
v___x_481_ = l_Lean_Expr_app___override(v___x_478_, v___x_480_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_481_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_483_);
v___x_485_ = v___x_471_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec(v_a_469_);
v___x_489_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_489_);
v___x_491_ = v___x_471_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_468_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_468_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref(v_arg_304_);
v___x_502_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_502_);
v___x_504_ = v___x_300_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_e_288_);
v_a_507_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_297_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_297_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_524_, lean_object* v_k_525_, uint8_t v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_526_ == 0)
{
lean_object* v___x_536_; lean_object* v_canon_537_; lean_object* v_cache_538_; lean_object* v___x_539_; 
v___x_536_ = lean_st_ref_get(v_a_528_);
v_canon_537_ = lean_ctor_get(v___x_536_, 9);
lean_inc_ref(v_canon_537_);
lean_dec(v___x_536_);
v_cache_538_ = lean_ctor_get(v_canon_537_, 0);
lean_inc_ref(v_cache_538_);
lean_dec_ref(v_canon_537_);
lean_inc_ref(v_e_524_);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_534_, v___x_535_, v_cache_538_, v_e_524_);
lean_dec_ref(v_cache_538_);
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_k_525_);
lean_dec_ref(v_e_524_);
v_val_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_val_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_539_);
v___x_548_ = lean_box(v_a_526_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
v___x_549_ = lean_apply_8(v_k_525_, v___x_548_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_588_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_588_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_canon_555_; lean_object* v_share_556_; lean_object* v_maxFVar_557_; lean_object* v_proofInstInfo_558_; lean_object* v_inferType_559_; lean_object* v_getLevel_560_; lean_object* v_congrInfo_561_; lean_object* v_defEqI_562_; lean_object* v_extensions_563_; lean_object* v_issues_564_; lean_object* v_instanceOverrides_565_; uint8_t v_debug_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_587_; 
v___x_554_ = lean_st_ref_take(v_a_528_);
v_canon_555_ = lean_ctor_get(v___x_554_, 9);
v_share_556_ = lean_ctor_get(v___x_554_, 0);
v_maxFVar_557_ = lean_ctor_get(v___x_554_, 1);
v_proofInstInfo_558_ = lean_ctor_get(v___x_554_, 2);
v_inferType_559_ = lean_ctor_get(v___x_554_, 3);
v_getLevel_560_ = lean_ctor_get(v___x_554_, 4);
v_congrInfo_561_ = lean_ctor_get(v___x_554_, 5);
v_defEqI_562_ = lean_ctor_get(v___x_554_, 6);
v_extensions_563_ = lean_ctor_get(v___x_554_, 7);
v_issues_564_ = lean_ctor_get(v___x_554_, 8);
v_instanceOverrides_565_ = lean_ctor_get(v___x_554_, 10);
v_debug_566_ = lean_ctor_get_uint8(v___x_554_, sizeof(void*)*11);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_587_ == 0)
{
v___x_568_ = v___x_554_;
v_isShared_569_ = v_isSharedCheck_587_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_instanceOverrides_565_);
lean_inc(v_canon_555_);
lean_inc(v_issues_564_);
lean_inc(v_extensions_563_);
lean_inc(v_defEqI_562_);
lean_inc(v_congrInfo_561_);
lean_inc(v_getLevel_560_);
lean_inc(v_inferType_559_);
lean_inc(v_proofInstInfo_558_);
lean_inc(v_maxFVar_557_);
lean_inc(v_share_556_);
lean_dec(v___x_554_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_587_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_cache_570_; lean_object* v_cacheInType_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_586_; 
v_cache_570_ = lean_ctor_get(v_canon_555_, 0);
v_cacheInType_571_ = lean_ctor_get(v_canon_555_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_canon_555_);
if (v_isSharedCheck_586_ == 0)
{
v___x_573_ = v_canon_555_;
v_isShared_574_ = v_isSharedCheck_586_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_cacheInType_571_);
lean_inc(v_cache_570_);
lean_dec(v_canon_555_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_586_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_a_550_);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_534_, v___x_535_, v_cache_570_, v_e_524_, v_a_550_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_cacheInType_571_);
v___x_577_ = v_reuseFailAlloc_585_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 9, v___x_577_);
v___x_579_ = v___x_568_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_share_556_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_maxFVar_557_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_proofInstInfo_558_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_inferType_559_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_getLevel_560_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v_congrInfo_561_);
lean_ctor_set(v_reuseFailAlloc_584_, 6, v_defEqI_562_);
lean_ctor_set(v_reuseFailAlloc_584_, 7, v_extensions_563_);
lean_ctor_set(v_reuseFailAlloc_584_, 8, v_issues_564_);
lean_ctor_set(v_reuseFailAlloc_584_, 9, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_584_, 10, v_instanceOverrides_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*11, v_debug_566_);
v___x_579_ = v_reuseFailAlloc_584_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_st_ref_put(v_a_528_, v___x_579_);
if (v_isShared_553_ == 0)
{
v___x_582_ = v___x_552_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_550_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_524_);
return v___x_549_;
}
}
}
else
{
lean_object* v___x_589_; lean_object* v_canon_590_; lean_object* v_cacheInType_591_; lean_object* v___x_592_; 
v___x_589_ = lean_st_ref_get(v_a_528_);
v_canon_590_ = lean_ctor_get(v___x_589_, 9);
lean_inc_ref(v_canon_590_);
lean_dec(v___x_589_);
v_cacheInType_591_ = lean_ctor_get(v_canon_590_, 1);
lean_inc_ref(v_cacheInType_591_);
lean_dec_ref(v_canon_590_);
lean_inc_ref(v_e_524_);
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_534_, v___x_535_, v_cacheInType_591_, v_e_524_);
lean_dec_ref(v_cacheInType_591_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_k_525_);
lean_dec_ref(v_e_524_);
v_val_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 0);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_val_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_592_);
v___x_601_ = lean_box(v_a_526_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
v___x_602_ = lean_apply_8(v_k_525_, v___x_601_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_641_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_641_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_641_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_641_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v_canon_608_; lean_object* v_share_609_; lean_object* v_maxFVar_610_; lean_object* v_proofInstInfo_611_; lean_object* v_inferType_612_; lean_object* v_getLevel_613_; lean_object* v_congrInfo_614_; lean_object* v_defEqI_615_; lean_object* v_extensions_616_; lean_object* v_issues_617_; lean_object* v_instanceOverrides_618_; uint8_t v_debug_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_640_; 
v___x_607_ = lean_st_ref_take(v_a_528_);
v_canon_608_ = lean_ctor_get(v___x_607_, 9);
v_share_609_ = lean_ctor_get(v___x_607_, 0);
v_maxFVar_610_ = lean_ctor_get(v___x_607_, 1);
v_proofInstInfo_611_ = lean_ctor_get(v___x_607_, 2);
v_inferType_612_ = lean_ctor_get(v___x_607_, 3);
v_getLevel_613_ = lean_ctor_get(v___x_607_, 4);
v_congrInfo_614_ = lean_ctor_get(v___x_607_, 5);
v_defEqI_615_ = lean_ctor_get(v___x_607_, 6);
v_extensions_616_ = lean_ctor_get(v___x_607_, 7);
v_issues_617_ = lean_ctor_get(v___x_607_, 8);
v_instanceOverrides_618_ = lean_ctor_get(v___x_607_, 10);
v_debug_619_ = lean_ctor_get_uint8(v___x_607_, sizeof(void*)*11);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_640_ == 0)
{
v___x_621_ = v___x_607_;
v_isShared_622_ = v_isSharedCheck_640_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_instanceOverrides_618_);
lean_inc(v_canon_608_);
lean_inc(v_issues_617_);
lean_inc(v_extensions_616_);
lean_inc(v_defEqI_615_);
lean_inc(v_congrInfo_614_);
lean_inc(v_getLevel_613_);
lean_inc(v_inferType_612_);
lean_inc(v_proofInstInfo_611_);
lean_inc(v_maxFVar_610_);
lean_inc(v_share_609_);
lean_dec(v___x_607_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_640_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_cache_623_; lean_object* v_cacheInType_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_639_; 
v_cache_623_ = lean_ctor_get(v_canon_608_, 0);
v_cacheInType_624_ = lean_ctor_get(v_canon_608_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_canon_608_);
if (v_isSharedCheck_639_ == 0)
{
v___x_626_ = v_canon_608_;
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_cacheInType_624_);
lean_inc(v_cache_623_);
lean_dec(v_canon_608_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
lean_inc(v_a_603_);
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_534_, v___x_535_, v_cacheInType_624_, v_e_524_, v_a_603_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_cache_623_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_638_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 9, v___x_630_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_share_609_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_maxFVar_610_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_proofInstInfo_611_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_inferType_612_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_getLevel_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_congrInfo_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_defEqI_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_extensions_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_issues_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 9, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 10, v_instanceOverrides_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_637_, sizeof(void*)*11, v_debug_619_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_st_ref_put(v_a_528_, v___x_632_);
if (v_isShared_606_ == 0)
{
v___x_635_ = v___x_605_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_603_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_524_);
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_642_, lean_object* v_k_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
uint8_t v_a_boxed_652_; lean_object* v_res_653_; 
v_a_boxed_652_ = lean_unbox(v_a_644_);
v_res_653_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_642_, v_k_643_, v_a_boxed_652_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_653_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = l_Lean_Expr_cleanupAnnotations(v_e_660_);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_663_ = l_Lean_Expr_isConstOf(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_Expr_isApp(v___x_661_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_661_);
return v___x_664_;
}
else
{
lean_object* v_arg_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_arg_665_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_arg_665_);
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_661_);
v___x_667_ = l_Lean_Expr_isApp(v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v___x_666_);
lean_dec_ref(v_arg_665_);
return v___x_667_;
}
else
{
lean_object* v_arg_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_arg_668_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_arg_668_);
v___x_669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_670_ = l_Lean_Expr_isApp(v___x_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___x_669_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_665_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_669_);
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_673_ = l_Lean_Expr_isConstOf(v___x_671_, v___x_672_);
lean_dec_ref(v___x_671_);
if (v___x_673_ == 0)
{
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_665_);
return v___x_673_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Expr_isBoolTrue(v_arg_668_);
if (v___x_674_ == 0)
{
lean_dec_ref(v_arg_665_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_Expr_isBoolTrue(v_arg_665_);
return v___x_675_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_661_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_Lean_Expr_cleanupAnnotations(v_e_682_);
v___x_684_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_685_ = l_Lean_Expr_isConstOf(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_Expr_isApp(v___x_683_);
if (v___x_686_ == 0)
{
lean_dec_ref(v___x_683_);
return v___x_686_;
}
else
{
lean_object* v_arg_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_arg_687_ = lean_ctor_get(v___x_683_, 1);
lean_inc_ref(v_arg_687_);
v___x_688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_683_);
v___x_689_ = l_Lean_Expr_isApp(v___x_688_);
if (v___x_689_ == 0)
{
lean_dec_ref(v___x_688_);
lean_dec_ref(v_arg_687_);
return v___x_689_;
}
else
{
lean_object* v_arg_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_arg_690_ = lean_ctor_get(v___x_688_, 1);
lean_inc_ref(v_arg_690_);
v___x_691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_688_);
v___x_692_ = l_Lean_Expr_isApp(v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_691_);
lean_dec_ref(v_arg_690_);
lean_dec_ref(v_arg_687_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_691_);
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_695_ = l_Lean_Expr_isConstOf(v___x_693_, v___x_694_);
lean_dec_ref(v___x_693_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_arg_690_);
lean_dec_ref(v_arg_687_);
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = l_Lean_Expr_isBoolFalse(v_arg_690_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_arg_687_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = l_Lean_Expr_isBoolTrue(v_arg_687_);
return v___x_697_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_683_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_698_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t v_x_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(v_x_701_);
v___x_703_ = lean_obj_tag_nat(v___x_702_);
lean_dec(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object* v_x_704_){
_start:
{
uint8_t v_x_4__boxed_705_; lean_object* v_res_706_; 
v_x_4__boxed_705_ = lean_unbox(v_x_704_);
v_res_706_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_4__boxed_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_707_){
_start:
{
lean_inc(v_k_707_);
return v_k_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_708_);
lean_dec(v_k_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_710_, lean_object* v_ctorIdx_711_, uint8_t v_t_712_, lean_object* v_h_713_, lean_object* v_k_714_){
_start:
{
lean_inc(v_k_714_);
return v_k_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_715_, lean_object* v_ctorIdx_716_, lean_object* v_t_717_, lean_object* v_h_718_, lean_object* v_k_719_){
_start:
{
uint8_t v_t_boxed_720_; lean_object* v_res_721_; 
v_t_boxed_720_ = lean_unbox(v_t_717_);
v_res_721_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_715_, v_ctorIdx_716_, v_t_boxed_720_, v_h_718_, v_k_719_);
lean_dec(v_k_719_);
lean_dec(v_ctorIdx_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_722_){
_start:
{
lean_inc(v_canonType_722_);
return v_canonType_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_723_);
lean_dec(v_canonType_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_725_, uint8_t v_t_726_, lean_object* v_h_727_, lean_object* v_canonType_728_){
_start:
{
lean_inc(v_canonType_728_);
return v_canonType_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_canonType_732_){
_start:
{
uint8_t v_t_boxed_733_; lean_object* v_res_734_; 
v_t_boxed_733_ = lean_unbox(v_t_730_);
v_res_734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_729_, v_t_boxed_733_, v_h_731_, v_canonType_732_);
lean_dec(v_canonType_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_735_){
_start:
{
lean_inc(v_canonInst_735_);
return v_canonInst_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_736_);
lean_dec(v_canonInst_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_738_, uint8_t v_t_739_, lean_object* v_h_740_, lean_object* v_canonInst_741_){
_start:
{
lean_inc(v_canonInst_741_);
return v_canonInst_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_canonInst_745_){
_start:
{
uint8_t v_t_boxed_746_; lean_object* v_res_747_; 
v_t_boxed_746_ = lean_unbox(v_t_743_);
v_res_747_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_742_, v_t_boxed_746_, v_h_744_, v_canonInst_745_);
lean_dec(v_canonInst_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_748_){
_start:
{
lean_inc(v_canonImplicit_748_);
return v_canonImplicit_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_749_);
lean_dec(v_canonImplicit_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_751_, uint8_t v_t_752_, lean_object* v_h_753_, lean_object* v_canonImplicit_754_){
_start:
{
lean_inc(v_canonImplicit_754_);
return v_canonImplicit_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_canonImplicit_758_){
_start:
{
uint8_t v_t_boxed_759_; lean_object* v_res_760_; 
v_t_boxed_759_ = lean_unbox(v_t_756_);
v_res_760_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_755_, v_t_boxed_759_, v_h_757_, v_canonImplicit_758_);
lean_dec(v_canonImplicit_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_761_){
_start:
{
lean_inc(v_visit_761_);
return v_visit_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_762_);
lean_dec(v_visit_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_764_, uint8_t v_t_765_, lean_object* v_h_766_, lean_object* v_visit_767_){
_start:
{
lean_inc(v_visit_767_);
return v_visit_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_visit_771_){
_start:
{
uint8_t v_t_boxed_772_; lean_object* v_res_773_; 
v_t_boxed_772_ = lean_unbox(v_t_769_);
v_res_773_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_768_, v_t_boxed_772_, v_h_770_, v_visit_771_);
lean_dec(v_visit_771_);
return v_res_773_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_788_, lean_object* v_x_789_){
_start:
{
switch(v_r_788_)
{
case 0:
{
lean_object* v___x_790_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_790_;
}
case 1:
{
lean_object* v___x_791_; 
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_791_;
}
case 2:
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_792_;
}
default: 
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_794_, lean_object* v_x_795_){
_start:
{
uint8_t v_r_boxed_796_; lean_object* v_res_797_; 
v_r_boxed_796_ = lean_unbox(v_r_794_);
v_res_797_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_796_, v_x_795_);
lean_dec(v_x_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_800_, lean_object* v_i_801_, lean_object* v_arg_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_array_get_size(v_pinfos_800_);
v___x_859_ = lean_nat_dec_lt(v_i_801_, v___x_858_);
if (v___x_859_ == 0)
{
v___y_809_ = v_a_803_;
v___y_810_ = v_a_804_;
v___y_811_ = v_a_805_;
v___y_812_ = v_a_806_;
goto v___jp_808_;
}
else
{
lean_object* v_pinfo_860_; uint8_t v_isInstance_861_; 
v_pinfo_860_ = lean_array_fget_borrowed(v_pinfos_800_, v_i_801_);
v_isInstance_861_ = lean_ctor_get_uint8(v_pinfo_860_, sizeof(void*)*1 + 4);
if (v_isInstance_861_ == 0)
{
uint8_t v_isProp_862_; 
v_isProp_862_ = lean_ctor_get_uint8(v_pinfo_860_, sizeof(void*)*1 + 2);
if (v_isProp_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_860_);
if (v___x_863_ == 0)
{
v___y_809_ = v_a_803_;
v___y_810_ = v_a_804_;
v___y_811_ = v_a_805_;
v___y_812_ = v_a_806_;
goto v___jp_808_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_isTypeFormer(v_arg_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_880_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
if (v___x_869_ == 0)
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_870_ = 2;
v___x_871_ = lean_box(v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = 0;
v___x_876_ = lean_box(v___x_875_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_876_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_864_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_864_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
else
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec_ref(v_arg_802_);
v___x_889_ = 3;
v___x_890_ = lean_box(v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
else
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_arg_802_);
v___x_892_ = 1;
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
v___jp_808_:
{
lean_object* v___x_813_; 
lean_inc_ref(v_arg_802_);
v___x_813_ = l_Lean_Meta_isProp(v_arg_802_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_849_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_849_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_849_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_849_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___x_818_; 
v___x_818_ = lean_unbox(v_a_814_);
lean_dec(v_a_814_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_del_object(v___x_816_);
v___x_819_ = l_Lean_Meta_isTypeFormer(v_arg_802_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_835_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_835_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_835_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_835_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = lean_unbox(v_a_820_);
lean_dec(v_a_820_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = 3;
v___x_826_ = lean_box(v___x_825_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_826_);
v___x_828_ = v___x_822_;
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
else
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = 0;
v___x_831_ = lean_box(v___x_830_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_831_);
v___x_833_ = v___x_822_;
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
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_819_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_819_);
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
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec_ref(v_arg_802_);
v___x_844_ = 3;
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_845_);
v___x_847_ = v___x_816_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_arg_802_);
v_a_850_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_813_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_813_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_895_, lean_object* v_i_896_, lean_object* v_arg_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_895_, v_i_896_, v_arg_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_i_896_);
lean_dec_ref(v_pinfos_895_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_904_, lean_object* v_offset_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v_offset_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = l_Lean_mkNatLit(v_offset_905_);
v___x_909_ = l_Lean_mkNatAdd(v_e_904_, v___x_908_);
return v___x_909_;
}
else
{
lean_dec(v_offset_905_);
return v_e_904_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_910_; lean_object* v_dummy_911_; 
v___x_910_ = lean_box(0);
v_dummy_911_ = l_Lean_Expr_sort___override(v___x_910_);
return v_dummy_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_912_, lean_object* v_e_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_fromClass_919_; 
v_fromClass_919_ = lean_ctor_get_uint8(v_info_912_, sizeof(void*)*3);
if (v_fromClass_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_913_, v_fromClass_919_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_956_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_956_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_956_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_956_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
if (lean_obj_tag(v_a_921_) == 1)
{
lean_object* v_val_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_923_);
v_val_925_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_val_925_);
lean_dec_ref_known(v_a_921_, 1);
v___x_926_ = l_Lean_Expr_getAppFn(v_val_925_);
v___x_927_ = l_Lean_Meta_reduceProj_x3f(v___x_926_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
if (lean_obj_tag(v_a_928_) == 0)
{
lean_dec(v_val_925_);
return v___x_927_;
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_950_; 
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_951_);
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_950_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_950_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_949_; 
v_val_932_ = lean_ctor_get(v_a_928_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_949_ == 0)
{
v___x_934_ = v_a_928_;
v_isShared_935_ = v_isSharedCheck_949_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v_a_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_949_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_dummy_936_; lean_object* v_nargs_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_dummy_936_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_937_ = l_Lean_Expr_getAppNumArgs(v_val_925_);
lean_inc(v_nargs_937_);
v___x_938_ = lean_mk_array(v_nargs_937_, v_dummy_936_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_sub(v_nargs_937_, v___x_939_);
lean_dec(v_nargs_937_);
v___x_941_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_925_, v___x_938_, v___x_940_);
v___x_942_ = l_Lean_mkAppN(v_val_932_, v___x_941_);
lean_dec_ref(v___x_941_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_942_);
v___x_944_ = v___x_934_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_944_);
v___x_946_ = v___x_930_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
else
{
lean_dec(v_val_925_);
return v___x_927_;
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v_a_921_);
v___x_952_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_952_);
v___x_954_ = v___x_923_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
return v___x_920_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_e_913_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_959_, lean_object* v_e_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_959_, v_e_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec_ref(v_info_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_967_, lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_967_, v_e_968_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_977_, lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_977_, v_e_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec_ref(v_info_977_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_987_){
_start:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_989_ = l_Lean_Expr_isConstOf(v_e_987_, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_990_){
_start:
{
uint8_t v_res_991_; lean_object* v_r_992_; 
v_res_991_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_990_);
lean_dec_ref(v_e_990_);
v_r_992_ = lean_box(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = l_Lean_Expr_cleanupAnnotations(v_e_1026_);
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_1029_ = l_Lean_Expr_isConstOf(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Expr_isApp(v___x_1027_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v___x_1027_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1027_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_1033_ = l_Lean_Expr_isConstOf(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Expr_isApp(v___x_1031_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v___x_1031_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1031_);
v___x_1036_ = l_Lean_Expr_isApp(v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1035_);
v___x_1038_ = l_Lean_Expr_isApp(v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec_ref(v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1037_);
v___x_1040_ = l_Lean_Expr_isApp(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec_ref(v___x_1039_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1039_);
v___x_1042_ = l_Lean_Expr_isApp(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_dec_ref(v___x_1041_);
return v___x_1042_;
}
else
{
lean_object* v_arg_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_arg_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc_ref(v_arg_1043_);
v___x_1044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1041_);
v___x_1045_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1046_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1048_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1050_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1052_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1054_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1053_);
lean_dec_ref(v___x_1044_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v_arg_1043_);
return v___x_1054_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1043_);
lean_dec_ref(v_arg_1043_);
return v___x_1055_;
}
}
else
{
uint8_t v___x_1056_; 
lean_dec_ref(v___x_1044_);
v___x_1056_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1043_);
lean_dec_ref(v_arg_1043_);
return v___x_1056_;
}
}
else
{
uint8_t v___x_1057_; 
lean_dec_ref(v___x_1044_);
v___x_1057_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1043_);
lean_dec_ref(v_arg_1043_);
return v___x_1057_;
}
}
else
{
uint8_t v___x_1058_; 
lean_dec_ref(v___x_1044_);
v___x_1058_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1043_);
lean_dec_ref(v_arg_1043_);
return v___x_1058_;
}
}
else
{
uint8_t v___x_1059_; 
lean_dec_ref(v___x_1044_);
v___x_1059_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1043_);
lean_dec_ref(v_arg_1043_);
return v___x_1059_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1031_);
return v___x_1033_;
}
}
}
else
{
lean_dec_ref(v___x_1027_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1060_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1069_, lean_object* v_inst_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
lean_inc_ref(v_inst_1070_);
lean_inc_ref(v_e_1069_);
v___x_1078_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1069_, v_inst_1070_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1129_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1129_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1129_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_unbox(v_a_1079_);
lean_dec(v_a_1079_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_del_object(v___x_1081_);
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1069_);
v___x_1085_ = l_Lean_indentExpr(v_e_1069_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_indentExpr(v_inst_1070_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1071_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1117_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1117_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1117_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v_verbose_1096_; 
v_verbose_1096_ = lean_ctor_get_uint8(v_a_1092_, 0);
lean_dec(v_a_1092_);
if (v_verbose_1096_ == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref_known(v___x_1090_, 2);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_e_1069_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_e_1069_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v___x_1100_; 
lean_del_object(v___x_1094_);
v___x_1100_ = l_Lean_Meta_Sym_reportIssue(v___x_1090_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1100_, 0);
lean_dec(v_unused_1108_);
v___x_1102_ = v___x_1100_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v___x_1100_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_e_1069_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_e_1069_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_e_1069_);
v_a_1109_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1100_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1100_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref_known(v___x_1090_, 2);
lean_dec_ref(v_e_1069_);
v_a_1118_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1091_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1091_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v_e_1069_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_inst_1070_);
v___x_1127_ = v___x_1081_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_inst_1070_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_inst_1070_);
lean_dec_ref(v_e_1069_);
v_a_1130_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1078_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1078_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1138_, lean_object* v_inst_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1138_, v_inst_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
return v_res_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1151_, lean_object* v_type_1152_, uint8_t v_report_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
lean_inc_ref(v_type_1152_);
v___x_1161_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1152_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1213_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1213_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1213_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
if (lean_obj_tag(v_a_1162_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
lean_del_object(v___x_1164_);
lean_dec_ref(v_type_1152_);
v_val_1166_ = lean_ctor_get(v_a_1162_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_a_1162_, 1);
v___x_1167_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1151_, v_val_1166_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
return v___x_1167_;
}
else
{
lean_dec(v_a_1162_);
if (v_report_1153_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v_type_1152_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_e_1151_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_e_1151_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_del_object(v___x_1164_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1151_);
v___x_1172_ = l_Lean_indentExpr(v_e_1151_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_indentExpr(v_type_1152_);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1154_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1204_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1204_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1204_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
uint8_t v_verbose_1183_; 
v_verbose_1183_ = lean_ctor_get_uint8(v_a_1179_, 0);
lean_dec(v_a_1179_);
if (v_verbose_1183_ == 0)
{
lean_object* v___x_1185_; 
lean_dec_ref_known(v___x_1177_, 2);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_e_1151_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_e_1151_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v___x_1187_; 
lean_del_object(v___x_1181_);
v___x_1187_ = l_Lean_Meta_Sym_reportIssue(v___x_1177_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1195_);
v___x_1189_ = v___x_1187_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_e_1151_);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_e_1151_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_e_1151_);
v_a_1196_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1187_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1187_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref_known(v___x_1177_, 2);
lean_dec_ref(v_e_1151_);
v_a_1205_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1178_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1178_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_type_1152_);
lean_dec_ref(v_e_1151_);
v_a_1214_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1161_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1161_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1222_, lean_object* v_type_1223_, lean_object* v_report_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v_report_boxed_1232_; lean_object* v_res_1233_; 
v_report_boxed_1232_ = lean_unbox(v_report_1224_);
v_res_1233_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1222_, v_type_1223_, v_report_boxed_1232_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1234_, lean_object* v_type_1235_, uint8_t v_report_1236_, uint8_t v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1234_, v_type_1235_, v_report_1236_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1246_, lean_object* v_type_1247_, lean_object* v_report_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
uint8_t v_report_boxed_1257_; uint8_t v_a_boxed_1258_; lean_object* v_res_1259_; 
v_report_boxed_1257_ = lean_unbox(v_report_1248_);
v_a_boxed_1258_ = lean_unbox(v_a_1249_);
v_res_1259_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1246_, v_type_1247_, v_report_boxed_1257_, v_a_boxed_1258_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1259_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
else
{
lean_object* v_key_1263_; lean_object* v_tail_1264_; uint8_t v___x_1265_; 
v_key_1263_ = lean_ctor_get(v_x_1261_, 0);
v_tail_1264_ = lean_ctor_get(v_x_1261_, 2);
v___x_1265_ = lean_expr_eqv(v_key_1263_, v_a_1260_);
if (v___x_1265_ == 0)
{
v_x_1261_ = v_tail_1264_;
goto _start;
}
else
{
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1267_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_a_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
if (lean_obj_tag(v_x_1272_) == 0)
{
return v_x_1271_;
}
else
{
lean_object* v_key_1273_; lean_object* v_value_1274_; lean_object* v_tail_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1298_; 
v_key_1273_ = lean_ctor_get(v_x_1272_, 0);
v_value_1274_ = lean_ctor_get(v_x_1272_, 1);
v_tail_1275_ = lean_ctor_get(v_x_1272_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1272_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1277_ = v_x_1272_;
v_isShared_1278_ = v_isSharedCheck_1298_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_tail_1275_);
lean_inc(v_value_1274_);
lean_inc(v_key_1273_);
lean_dec(v_x_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1298_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v_fold_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1279_ = lean_array_get_size(v_x_1271_);
v___x_1280_ = l_Lean_Expr_hash(v_key_1273_);
v___x_1281_ = 32ULL;
v___x_1282_ = lean_uint64_shift_right(v___x_1280_, v___x_1281_);
v_fold_1283_ = lean_uint64_xor(v___x_1280_, v___x_1282_);
v___x_1284_ = 16ULL;
v___x_1285_ = lean_uint64_shift_right(v_fold_1283_, v___x_1284_);
v___x_1286_ = lean_uint64_xor(v_fold_1283_, v___x_1285_);
v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
v___x_1288_ = lean_usize_of_nat(v___x_1279_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_sub(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_usize_land(v___x_1287_, v___x_1290_);
v___x_1292_ = lean_array_uget_borrowed(v_x_1271_, v___x_1291_);
lean_inc(v___x_1292_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 2, v___x_1292_);
v___x_1294_ = v___x_1277_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_key_1273_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_value_1274_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_array_uset(v_x_1271_, v___x_1291_, v___x_1294_);
v_x_1271_ = v___x_1295_;
v_x_1272_ = v_tail_1275_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object* v_i_1299_, lean_object* v_source_1300_, lean_object* v_target_1301_){
_start:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_array_get_size(v_source_1300_);
v___x_1303_ = lean_nat_dec_lt(v_i_1299_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v_source_1300_);
lean_dec(v_i_1299_);
return v_target_1301_;
}
else
{
lean_object* v_es_1304_; lean_object* v___x_1305_; lean_object* v_source_1306_; lean_object* v_target_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_es_1304_ = lean_array_fget(v_source_1300_, v_i_1299_);
v___x_1305_ = lean_box(0);
v_source_1306_ = lean_array_fset(v_source_1300_, v_i_1299_, v___x_1305_);
v_target_1307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_target_1301_, v_es_1304_);
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_nat_add(v_i_1299_, v___x_1308_);
lean_dec(v_i_1299_);
v_i_1299_ = v___x_1309_;
v_source_1300_ = v_source_1306_;
v_target_1301_ = v_target_1307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_nbuckets_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1312_ = lean_array_get_size(v_data_1311_);
v___x_1313_ = lean_unsigned_to_nat(2u);
v_nbuckets_1314_ = lean_nat_mul(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_mk_array(v_nbuckets_1314_, v___x_1316_);
v___x_1318_ = lean_array_propagate_mark(v_data_1311_, v___x_1317_);
v___x_1319_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v___x_1315_, v_data_1311_, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1320_, lean_object* v_b_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_dec(v_b_1321_);
lean_dec_ref(v_a_1320_);
return v_x_1322_;
}
else
{
lean_object* v_key_1323_; lean_object* v_value_1324_; lean_object* v_tail_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1337_; 
v_key_1323_ = lean_ctor_get(v_x_1322_, 0);
v_value_1324_ = lean_ctor_get(v_x_1322_, 1);
v_tail_1325_ = lean_ctor_get(v_x_1322_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1327_ = v_x_1322_;
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_tail_1325_);
lean_inc(v_value_1324_);
lean_inc(v_key_1323_);
lean_dec(v_x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_expr_eqv(v_key_1323_, v_a_1320_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1320_, v_b_1321_, v_tail_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 2, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_key_1323_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_value_1324_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v___x_1335_; 
lean_dec(v_value_1324_);
lean_dec(v_key_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_b_1321_);
lean_ctor_set(v___x_1327_, 0, v_a_1320_);
v___x_1335_ = v___x_1327_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_b_1321_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_tail_1325_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1338_, lean_object* v_a_1339_, lean_object* v_b_1340_){
_start:
{
lean_object* v_size_1341_; lean_object* v_buckets_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1385_; 
v_size_1341_ = lean_ctor_get(v_m_1338_, 0);
v_buckets_1342_ = lean_ctor_get(v_m_1338_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_m_1338_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1344_ = v_m_1338_;
v_isShared_1345_ = v_isSharedCheck_1385_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_buckets_1342_);
lean_inc(v_size_1341_);
lean_dec(v_m_1338_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1385_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v_fold_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v_bkt_1359_; uint8_t v___x_1360_; 
v___x_1346_ = lean_array_get_size(v_buckets_1342_);
v___x_1347_ = l_Lean_Expr_hash(v_a_1339_);
v___x_1348_ = 32ULL;
v___x_1349_ = lean_uint64_shift_right(v___x_1347_, v___x_1348_);
v_fold_1350_ = lean_uint64_xor(v___x_1347_, v___x_1349_);
v___x_1351_ = 16ULL;
v___x_1352_ = lean_uint64_shift_right(v_fold_1350_, v___x_1351_);
v___x_1353_ = lean_uint64_xor(v_fold_1350_, v___x_1352_);
v___x_1354_ = lean_uint64_to_usize(v___x_1353_);
v___x_1355_ = lean_usize_of_nat(v___x_1346_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_sub(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_usize_land(v___x_1354_, v___x_1357_);
v_bkt_1359_ = lean_array_uget_borrowed(v_buckets_1342_, v___x_1358_);
v___x_1360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1339_, v_bkt_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v_size_x27_1362_; lean_object* v___x_1363_; lean_object* v_buckets_x27_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
v_size_x27_1362_ = lean_nat_add(v_size_1341_, v___x_1361_);
lean_dec(v_size_1341_);
lean_inc(v_bkt_1359_);
v___x_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1363_, 0, v_a_1339_);
lean_ctor_set(v___x_1363_, 1, v_b_1340_);
lean_ctor_set(v___x_1363_, 2, v_bkt_1359_);
v_buckets_x27_1364_ = lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(4u);
v___x_1366_ = lean_nat_mul(v_size_x27_1362_, v___x_1365_);
v___x_1367_ = lean_unsigned_to_nat(3u);
v___x_1368_ = lean_nat_div(v___x_1366_, v___x_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_array_get_size(v_buckets_x27_1364_);
v___x_1370_ = lean_nat_dec_le(v___x_1368_, v___x_1369_);
lean_dec(v___x_1368_);
if (v___x_1370_ == 0)
{
lean_object* v_val_1371_; lean_object* v___x_1373_; 
v_val_1371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1364_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_val_1371_);
lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
v___x_1373_ = v___x_1344_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_size_x27_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_val_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1376_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_buckets_x27_1364_);
lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
v___x_1376_ = v___x_1344_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_size_x27_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_buckets_x27_1364_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v_buckets_x27_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_inc(v_bkt_1359_);
v___x_1378_ = lean_box(0);
v_buckets_x27_1379_ = lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1378_);
v___x_1380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1339_, v_b_1340_, v_bkt_1359_);
v___x_1381_ = lean_array_uset(v_buckets_x27_1379_, v___x_1358_, v___x_1380_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1381_);
v___x_1383_ = v___x_1344_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_size_1341_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object* v_k_1386_, uint8_t v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_box(v___y_1387_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
v___x_1397_ = lean_apply_9(v_k_1386_, v_b_1390_, v___x_1396_, v___y_1388_, v___y_1389_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, lean_box(0));
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object* v_k_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___y_61767__boxed_1408_; lean_object* v_res_1409_; 
v___y_61767__boxed_1408_ = lean_unbox(v___y_1399_);
v_res_1409_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1398_, v___y_61767__boxed_1408_, v___y_1400_, v___y_1401_, v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object* v_name_1410_, uint8_t v_bi_1411_, lean_object* v_type_1412_, lean_object* v_k_1413_, uint8_t v_kind_1414_, uint8_t v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(v___y_1415_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1424_, 0, v_k_1413_);
lean_closure_set(v___f_1424_, 1, v___x_1423_);
lean_closure_set(v___f_1424_, 2, v___y_1416_);
lean_closure_set(v___f_1424_, 3, v___y_1417_);
v___x_1425_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1410_, v_bi_1411_, v_type_1412_, v___f_1424_, v_kind_1414_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1425_) == 0)
{
return v___x_1425_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object* v_name_1434_, lean_object* v_bi_1435_, lean_object* v_type_1436_, lean_object* v_k_1437_, lean_object* v_kind_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_bi_boxed_1447_; uint8_t v_kind_boxed_1448_; uint8_t v___y_61795__boxed_1449_; lean_object* v_res_1450_; 
v_bi_boxed_1447_ = lean_unbox(v_bi_1435_);
v_kind_boxed_1448_ = lean_unbox(v_kind_1438_);
v___y_61795__boxed_1449_ = lean_unbox(v___y_1439_);
v_res_1450_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1434_, v_bi_boxed_1447_, v_type_1436_, v_k_1437_, v_kind_boxed_1448_, v___y_61795__boxed_1449_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v_env_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1454_ = lean_st_ref_get(v___y_1452_);
v_env_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc_ref(v_env_1455_);
lean_dec(v___x_1454_);
v___x_1456_ = l_Lean_Meta_isMatcherCore(v_env_1455_, v_declName_1451_);
v___x_1457_ = lean_box(v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1459_, v___y_1460_);
lean_dec(v___y_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_env_1470_; uint8_t v___x_1471_; lean_object* v_env_1472_; lean_object* v___x_1473_; lean_object* v_toCold_1474_; lean_object* v_mctx_1475_; lean_object* v_lctx_1476_; lean_object* v_options_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1469_ = lean_st_ref_get(v___y_1467_);
v_env_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc_ref(v_env_1470_);
lean_dec(v___x_1469_);
v___x_1471_ = 0;
v_env_1472_ = l_Lean_Environment_setRecordingDeps(v_env_1470_, v___x_1471_);
v___x_1473_ = lean_st_ref_get(v___y_1465_);
v_toCold_1474_ = lean_ctor_get(v___y_1466_, 0);
v_mctx_1475_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_mctx_1475_);
lean_dec(v___x_1473_);
v_lctx_1476_ = lean_ctor_get(v___y_1464_, 2);
v_options_1477_ = lean_ctor_get(v_toCold_1474_, 2);
lean_inc_ref(v_options_1477_);
lean_inc_ref(v_lctx_1476_);
v___x_1478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1478_, 0, v_env_1472_);
lean_ctor_set(v___x_1478_, 1, v_mctx_1475_);
lean_ctor_set(v___x_1478_, 2, v_lctx_1476_);
lean_ctor_set(v___x_1478_, 3, v_options_1477_);
v___x_1479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v_msgData_1463_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1488_; double v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_float_of_nat(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1547_; 
v_ref_1500_ = lean_ctor_get(v___y_1497_, 2);
v___x_1501_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1547_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1547_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v_traceState_1507_; lean_object* v_env_1508_; lean_object* v_nextMacroScope_1509_; lean_object* v_ngen_1510_; lean_object* v_auxDeclNGen_1511_; lean_object* v_cache_1512_; lean_object* v_recordedDeps_1513_; lean_object* v_messages_1514_; lean_object* v_infoState_1515_; lean_object* v_snapshotTasks_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1546_; 
v___x_1506_ = lean_st_ref_take(v___y_1498_);
v_traceState_1507_ = lean_ctor_get(v___x_1506_, 4);
v_env_1508_ = lean_ctor_get(v___x_1506_, 0);
v_nextMacroScope_1509_ = lean_ctor_get(v___x_1506_, 1);
v_ngen_1510_ = lean_ctor_get(v___x_1506_, 2);
v_auxDeclNGen_1511_ = lean_ctor_get(v___x_1506_, 3);
v_cache_1512_ = lean_ctor_get(v___x_1506_, 5);
v_recordedDeps_1513_ = lean_ctor_get(v___x_1506_, 6);
v_messages_1514_ = lean_ctor_get(v___x_1506_, 7);
v_infoState_1515_ = lean_ctor_get(v___x_1506_, 8);
v_snapshotTasks_1516_ = lean_ctor_get(v___x_1506_, 9);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1518_ = v___x_1506_;
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snapshotTasks_1516_);
lean_inc(v_infoState_1515_);
lean_inc(v_messages_1514_);
lean_inc(v_recordedDeps_1513_);
lean_inc(v_cache_1512_);
lean_inc(v_traceState_1507_);
lean_inc(v_auxDeclNGen_1511_);
lean_inc(v_ngen_1510_);
lean_inc(v_nextMacroScope_1509_);
lean_inc(v_env_1508_);
lean_dec(v___x_1506_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint64_t v_tid_1520_; lean_object* v_traces_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_tid_1520_ = lean_ctor_get_uint64(v_traceState_1507_, sizeof(void*)*1);
v_traces_1521_ = lean_ctor_get(v_traceState_1507_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_traceState_1507_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1523_ = v_traceState_1507_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_traces_1521_);
lean_dec(v_traceState_1507_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; double v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1528_ = 0;
v___x_1529_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1530_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1530_, 0, v_cls_1493_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
lean_ctor_set_float(v___x_1530_, sizeof(void*)*3, v___x_1527_);
lean_ctor_set_float(v___x_1530_, sizeof(void*)*3 + 8, v___x_1527_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*3 + 16, v___x_1528_);
v___x_1531_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1532_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v_a_1502_);
lean_ctor_set(v___x_1532_, 2, v___x_1531_);
lean_inc(v_ref_1500_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_ref_1500_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_PersistentArray_push___redArg(v_traces_1521_, v___x_1533_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1534_);
v___x_1536_ = v___x_1523_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1534_);
lean_ctor_set_uint64(v_reuseFailAlloc_1544_, sizeof(void*)*1, v_tid_1520_);
v___x_1536_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1536_);
v___x_1538_ = v___x_1518_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_env_1508_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_nextMacroScope_1509_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_ngen_1510_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_auxDeclNGen_1511_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v_cache_1512_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_recordedDeps_1513_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_messages_1514_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_infoState_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 9, v_snapshotTasks_1516_);
v___x_1538_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_st_ref_put(v___y_1498_, v___x_1538_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1525_);
v___x_1541_ = v___x_1504_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1525_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1548_, v_msg_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_box(0);
return v___x_1558_;
}
else
{
lean_object* v_key_1559_; lean_object* v_value_1560_; lean_object* v_tail_1561_; uint8_t v___x_1562_; 
v_key_1559_ = lean_ctor_get(v_x_1557_, 0);
v_value_1560_ = lean_ctor_get(v_x_1557_, 1);
v_tail_1561_ = lean_ctor_get(v_x_1557_, 2);
v___x_1562_ = lean_expr_eqv(v_key_1559_, v_a_1556_);
if (v___x_1562_ == 0)
{
v_x_1557_ = v_tail_1561_;
goto _start;
}
else
{
lean_object* v___x_1564_; 
lean_inc(v_value_1560_);
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_value_1560_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1565_, v_x_1566_);
lean_dec(v_x_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_buckets_1570_; lean_object* v___x_1571_; uint64_t v___x_1572_; uint64_t v___x_1573_; uint64_t v___x_1574_; uint64_t v_fold_1575_; uint64_t v___x_1576_; uint64_t v___x_1577_; uint64_t v___x_1578_; size_t v___x_1579_; size_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_buckets_1570_ = lean_ctor_get(v_m_1568_, 1);
v___x_1571_ = lean_array_get_size(v_buckets_1570_);
v___x_1572_ = l_Lean_Expr_hash(v_a_1569_);
v___x_1573_ = 32ULL;
v___x_1574_ = lean_uint64_shift_right(v___x_1572_, v___x_1573_);
v_fold_1575_ = lean_uint64_xor(v___x_1572_, v___x_1574_);
v___x_1576_ = 16ULL;
v___x_1577_ = lean_uint64_shift_right(v_fold_1575_, v___x_1576_);
v___x_1578_ = lean_uint64_xor(v_fold_1575_, v___x_1577_);
v___x_1579_ = lean_uint64_to_usize(v___x_1578_);
v___x_1580_ = lean_usize_of_nat(v___x_1571_);
v___x_1581_ = ((size_t)1ULL);
v___x_1582_ = lean_usize_sub(v___x_1580_, v___x_1581_);
v___x_1583_ = lean_usize_land(v___x_1579_, v___x_1582_);
v___x_1584_ = lean_array_uget_borrowed(v_buckets_1570_, v___x_1583_);
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1569_, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1586_, v_a_1587_);
lean_dec_ref(v_a_1587_);
lean_dec_ref(v_m_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_env_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = lean_st_ref_get(v___y_1590_);
v_env_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc_ref(v_env_1593_);
lean_dec(v___x_1592_);
v___x_1594_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1593_, v_declName_1589_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1596_, v___y_1597_);
lean_dec(v___y_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object* v_name_1600_, lean_object* v_type_1601_, lean_object* v_val_1602_, lean_object* v_k_1603_, uint8_t v_nondep_1604_, uint8_t v_kind_1605_, uint8_t v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_box(v___y_1606_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1615_, 0, v_k_1603_);
lean_closure_set(v___f_1615_, 1, v___x_1614_);
lean_closure_set(v___f_1615_, 2, v___y_1607_);
lean_closure_set(v___f_1615_, 3, v___y_1608_);
v___x_1616_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1600_, v_type_1601_, v_val_1602_, v___f_1615_, v_nondep_1604_, v_kind_1605_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1616_) == 0)
{
return v___x_1616_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object* v_name_1625_, lean_object* v_type_1626_, lean_object* v_val_1627_, lean_object* v_k_1628_, lean_object* v_nondep_1629_, lean_object* v_kind_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v_nondep_boxed_1639_; uint8_t v_kind_boxed_1640_; uint8_t v___y_62044__boxed_1641_; lean_object* v_res_1642_; 
v_nondep_boxed_1639_ = lean_unbox(v_nondep_1629_);
v_kind_boxed_1640_ = lean_unbox(v_kind_1630_);
v___y_62044__boxed_1641_ = lean_unbox(v___y_1631_);
v_res_1642_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1625_, v_type_1626_, v_val_1627_, v_k_1628_, v_nondep_boxed_1639_, v_kind_boxed_1640_, v___y_62044__boxed_1641_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = l_Lean_instInhabitedExpr;
v___x_1645_ = lean_panic_fn_borrowed(v___x_1644_, v_msg_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1646_, lean_object* v_body_1647_, lean_object* v_x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___y_62217__boxed_1657_; lean_object* v_res_1658_; 
v___y_62217__boxed_1657_ = lean_unbox(v___y_1649_);
v_res_1658_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1646_, v_body_1647_, v_x_1648_, v___y_62217__boxed_1657_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1661_, lean_object* v_body_1662_, lean_object* v_x_1663_, uint8_t v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_array_push(v_fvars_1661_, v_x_1663_);
v___x_1673_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1672_, v_body_1662_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1674_, lean_object* v_body_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___y_62228__boxed_1685_; lean_object* v_res_1686_; 
v___y_62228__boxed_1685_ = lean_unbox(v___y_1677_);
v_res_1686_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1674_, v_body_1675_, v_x_1676_, v___y_62228__boxed_1685_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1687_, lean_object* v_e_1688_, uint8_t v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
if (lean_obj_tag(v_e_1688_) == 6)
{
lean_object* v_binderName_1697_; lean_object* v_binderType_1698_; lean_object* v_body_1699_; uint8_t v_binderInfo_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_binderName_1697_ = lean_ctor_get(v_e_1688_, 0);
lean_inc(v_binderName_1697_);
v_binderType_1698_ = lean_ctor_get(v_e_1688_, 1);
lean_inc_ref(v_binderType_1698_);
v_body_1699_ = lean_ctor_get(v_e_1688_, 2);
lean_inc_ref(v_body_1699_);
v_binderInfo_1700_ = lean_ctor_get_uint8(v_e_1688_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1688_, 3);
lean_inc_ref(v_fvars_1687_);
v___f_1701_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1701_, 0, v_fvars_1687_);
lean_closure_set(v___f_1701_, 1, v_body_1699_);
v___x_1702_ = lean_expr_instantiate_rev(v_binderType_1698_, v_fvars_1687_);
lean_dec_ref(v_fvars_1687_);
lean_dec_ref(v_binderType_1698_);
v___x_1703_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1702_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = 0;
v___x_1706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_1697_, v_binderInfo_1700_, v_a_1704_, v___f_1701_, v___x_1705_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1706_;
}
else
{
lean_dec_ref(v___f_1701_);
lean_dec(v_binderName_1697_);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_expr_instantiate_rev(v_e_1688_, v_fvars_1687_);
lean_dec_ref(v_e_1688_);
v___x_1708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1707_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; uint8_t v___x_1710_; uint8_t v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = 0;
v___x_1711_ = 1;
v___x_1712_ = 1;
v___x_1713_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1687_, v_a_1709_, v___x_1710_, v___x_1711_, v___x_1710_, v___x_1711_, v___x_1712_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec_ref(v_fvars_1687_);
return v___x_1713_;
}
else
{
lean_dec_ref(v_fvars_1687_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1714_, uint8_t v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
if (v_a_1715_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1724_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1723_, v_e_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1726_ = l_Lean_Meta_Sym_etaReduce(v_e_1714_);
lean_dec_ref(v_e_1714_);
v___x_1727_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1725_, v___x_1726_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1728_, lean_object* v_body_1729_, lean_object* v_x_1730_, uint8_t v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_array_push(v_fvars_1728_, v_x_1730_);
v___x_1740_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1739_, v_body_1729_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1741_, lean_object* v_body_1742_, lean_object* v_x_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___y_62239__boxed_1752_; lean_object* v_res_1753_; 
v___y_62239__boxed_1752_ = lean_unbox(v___y_1744_);
v_res_1753_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1741_, v_body_1742_, v_x_1743_, v___y_62239__boxed_1752_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1754_, lean_object* v_e_1755_, uint8_t v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
if (lean_obj_tag(v_e_1755_) == 8)
{
lean_object* v_declName_1764_; lean_object* v_type_1765_; lean_object* v_value_1766_; lean_object* v_body_1767_; uint8_t v_nondep_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_declName_1764_ = lean_ctor_get(v_e_1755_, 0);
lean_inc(v_declName_1764_);
v_type_1765_ = lean_ctor_get(v_e_1755_, 1);
lean_inc_ref(v_type_1765_);
v_value_1766_ = lean_ctor_get(v_e_1755_, 2);
lean_inc_ref(v_value_1766_);
v_body_1767_ = lean_ctor_get(v_e_1755_, 3);
lean_inc_ref(v_body_1767_);
v_nondep_1768_ = lean_ctor_get_uint8(v_e_1755_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1755_, 4);
lean_inc_ref(v_fvars_1754_);
v___f_1769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1769_, 0, v_fvars_1754_);
lean_closure_set(v___f_1769_, 1, v_body_1767_);
v___x_1770_ = lean_expr_instantiate_rev(v_type_1765_, v_fvars_1754_);
lean_dec_ref(v_type_1765_);
v___x_1771_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1770_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_expr_instantiate_rev(v_value_1766_, v_fvars_1754_);
lean_dec_ref(v_fvars_1754_);
lean_dec_ref(v_value_1766_);
v___x_1774_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1773_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = 0;
v___x_1777_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_declName_1764_, v_a_1772_, v_a_1775_, v___f_1769_, v_nondep_1768_, v___x_1776_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
return v___x_1777_;
}
else
{
lean_dec(v_a_1772_);
lean_dec_ref(v___f_1769_);
lean_dec(v_declName_1764_);
return v___x_1774_;
}
}
else
{
lean_dec_ref(v___f_1769_);
lean_dec_ref(v_value_1766_);
lean_dec(v_declName_1764_);
lean_dec_ref(v_fvars_1754_);
return v___x_1771_;
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_expr_instantiate_rev(v_e_1755_, v_fvars_1754_);
lean_dec_ref(v_e_1755_);
v___x_1779_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1778_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; uint8_t v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = 1;
v___x_1782_ = 0;
v___x_1783_ = 1;
v___x_1784_ = l_Lean_Meta_mkLetFVars(v_fvars_1754_, v_a_1780_, v___x_1781_, v___x_1782_, v___x_1783_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
lean_dec_ref(v_fvars_1754_);
return v___x_1784_;
}
else
{
lean_dec_ref(v_fvars_1754_);
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1785_, uint8_t v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
if (v_a_1786_ == 0)
{
uint8_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = 1;
v___x_1795_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1785_, v___x_1794_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1797_, uint8_t v_report_1798_, uint8_t v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; 
lean_inc(v_a_1805_);
lean_inc_ref(v_a_1804_);
lean_inc(v_a_1803_);
lean_inc_ref(v_a_1802_);
lean_inc_ref(v_e_1797_);
v___x_1807_ = lean_infer_type(v_e_1797_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_n(v_a_1808_, 2);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = l_Lean_Meta_isProp(v_a_1808_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1822_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1822_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1822_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
if (v_a_1799_ == 0)
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_unbox(v_a_1810_);
lean_dec(v_a_1810_);
if (v___x_1818_ == 0)
{
lean_del_object(v___x_1812_);
goto v___jp_1814_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_a_1808_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v_e_1797_);
v___x_1820_ = v___x_1812_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_e_1797_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_del_object(v___x_1812_);
lean_dec(v_a_1810_);
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1808_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v___x_1817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1797_, v_a_1816_, v_report_1798_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1817_;
}
else
{
lean_dec_ref(v_e_1797_);
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1808_);
lean_dec_ref(v_e_1797_);
v_a_1823_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1809_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1809_);
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
else
{
lean_dec_ref(v_e_1797_);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1831_, uint8_t v_report_1832_, uint8_t v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
if (v_a_1833_ == 0)
{
lean_object* v___x_1841_; lean_object* v_canon_1842_; lean_object* v_cache_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_st_ref_get(v_a_1835_);
v_canon_1842_ = lean_ctor_get(v___x_1841_, 9);
lean_inc_ref(v_canon_1842_);
lean_dec(v___x_1841_);
v_cache_1843_ = lean_ctor_get(v_canon_1842_, 0);
lean_inc_ref(v_cache_1843_);
lean_dec_ref(v_canon_1842_);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1843_, v_e_1831_);
lean_dec_ref(v_cache_1843_);
if (lean_obj_tag(v___x_1844_) == 1)
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v_e_1831_);
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
lean_inc_ref(v_e_1831_);
v___x_1853_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1831_, v_report_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
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
v___x_1858_ = lean_st_ref_take(v_a_1835_);
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
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1874_, v_e_1831_, v_a_1854_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_cacheInType_1875_);
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
v___x_1884_ = lean_st_ref_put(v_a_1835_, v___x_1883_);
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
lean_dec_ref(v_e_1831_);
return v___x_1853_;
}
}
}
else
{
lean_object* v___x_1893_; lean_object* v_canon_1894_; lean_object* v_cacheInType_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_st_ref_get(v_a_1835_);
v_canon_1894_ = lean_ctor_get(v___x_1893_, 9);
lean_inc_ref(v_canon_1894_);
lean_dec(v___x_1893_);
v_cacheInType_1895_ = lean_ctor_get(v_canon_1894_, 1);
lean_inc_ref(v_cacheInType_1895_);
lean_dec_ref(v_canon_1894_);
v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1895_, v_e_1831_);
lean_dec_ref(v_cacheInType_1895_);
if (lean_obj_tag(v___x_1896_) == 1)
{
lean_object* v_val_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_e_1831_);
v_val_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_val_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 0);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_val_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_object* v___x_1905_; 
lean_dec(v___x_1896_);
lean_inc_ref(v_e_1831_);
v___x_1905_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1831_, v_report_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1944_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1944_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1944_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v_canon_1911_; lean_object* v_share_1912_; lean_object* v_maxFVar_1913_; lean_object* v_proofInstInfo_1914_; lean_object* v_inferType_1915_; lean_object* v_getLevel_1916_; lean_object* v_congrInfo_1917_; lean_object* v_defEqI_1918_; lean_object* v_extensions_1919_; lean_object* v_issues_1920_; lean_object* v_instanceOverrides_1921_; uint8_t v_debug_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1943_; 
v___x_1910_ = lean_st_ref_take(v_a_1835_);
v_canon_1911_ = lean_ctor_get(v___x_1910_, 9);
v_share_1912_ = lean_ctor_get(v___x_1910_, 0);
v_maxFVar_1913_ = lean_ctor_get(v___x_1910_, 1);
v_proofInstInfo_1914_ = lean_ctor_get(v___x_1910_, 2);
v_inferType_1915_ = lean_ctor_get(v___x_1910_, 3);
v_getLevel_1916_ = lean_ctor_get(v___x_1910_, 4);
v_congrInfo_1917_ = lean_ctor_get(v___x_1910_, 5);
v_defEqI_1918_ = lean_ctor_get(v___x_1910_, 6);
v_extensions_1919_ = lean_ctor_get(v___x_1910_, 7);
v_issues_1920_ = lean_ctor_get(v___x_1910_, 8);
v_instanceOverrides_1921_ = lean_ctor_get(v___x_1910_, 10);
v_debug_1922_ = lean_ctor_get_uint8(v___x_1910_, sizeof(void*)*11);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1924_ = v___x_1910_;
v_isShared_1925_ = v_isSharedCheck_1943_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_instanceOverrides_1921_);
lean_inc(v_canon_1911_);
lean_inc(v_issues_1920_);
lean_inc(v_extensions_1919_);
lean_inc(v_defEqI_1918_);
lean_inc(v_congrInfo_1917_);
lean_inc(v_getLevel_1916_);
lean_inc(v_inferType_1915_);
lean_inc(v_proofInstInfo_1914_);
lean_inc(v_maxFVar_1913_);
lean_inc(v_share_1912_);
lean_dec(v___x_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1943_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_cache_1926_; lean_object* v_cacheInType_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1942_; 
v_cache_1926_ = lean_ctor_get(v_canon_1911_, 0);
v_cacheInType_1927_ = lean_ctor_get(v_canon_1911_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_canon_1911_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1929_ = v_canon_1911_;
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_cacheInType_1927_);
lean_inc(v_cache_1926_);
lean_dec(v_canon_1911_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
lean_inc(v_a_1906_);
v___x_1931_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1927_, v_e_1831_, v_a_1906_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_cache_1926_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 9, v___x_1933_);
v___x_1935_ = v___x_1924_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_share_1912_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_maxFVar_1913_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_proofInstInfo_1914_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_inferType_1915_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_getLevel_1916_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v_congrInfo_1917_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_defEqI_1918_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_extensions_1919_);
lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_issues_1920_);
lean_ctor_set(v_reuseFailAlloc_1940_, 9, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1940_, 10, v_instanceOverrides_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1940_, sizeof(void*)*11, v_debug_1922_);
v___x_1935_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_st_ref_put(v_a_1835_, v___x_1935_);
if (v_isShared_1909_ == 0)
{
v___x_1938_ = v___x_1908_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1906_);
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
else
{
lean_dec_ref(v_e_1831_);
return v___x_1905_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1961_ = l_Lean_mkConst(v___x_1960_, v___x_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1962_, lean_object* v_prop_1963_, lean_object* v_inst_1964_, lean_object* v_e_1965_, uint8_t v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; 
lean_inc_ref(v_prop_1963_);
v___x_1974_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1963_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2017_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2017_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2017_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___y_1980_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1975_);
v___x_1986_ = l_Lean_Expr_app___override(v___x_1985_, v_a_1975_);
if (v_a_1966_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1986_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___y_1990_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_a_1988_) == 0)
{
lean_inc_ref(v_inst_1964_);
v___y_1990_ = v_inst_1964_;
goto v___jp_1989_;
}
else
{
lean_object* v_val_2006_; 
v_val_2006_ = lean_ctor_get(v_a_1988_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v_a_1988_, 1);
v___y_1990_ = v_val_2006_;
goto v___jp_1989_;
}
v___jp_1989_:
{
lean_object* v___x_1991_; 
lean_inc_ref(v_inst_1964_);
v___x_1991_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1964_, v___y_1990_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2005_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2005_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2005_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_ptr_addr(v_prop_1963_);
lean_dec_ref(v_prop_1963_);
v___x_1997_ = lean_ptr_addr(v_a_1975_);
v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_del_object(v___x_1994_);
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_inst_1964_);
v___y_1980_ = v_a_1992_;
goto v___jp_1979_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_ptr_addr(v_inst_1964_);
lean_dec_ref(v_inst_1964_);
v___x_2000_ = lean_ptr_addr(v_a_1992_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_del_object(v___x_1994_);
lean_dec_ref(v_e_1965_);
v___y_1980_ = v_a_1992_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2003_; 
lean_dec(v_a_1992_);
lean_del_object(v___x_1977_);
lean_dec(v_a_1975_);
lean_dec_ref(v_g_1962_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_e_1965_);
v___x_2003_ = v___x_1994_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_e_1965_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_del_object(v___x_1977_);
lean_dec(v_a_1975_);
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_inst_1964_);
lean_dec_ref(v_prop_1963_);
lean_dec_ref(v_g_1962_);
return v___x_1991_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_del_object(v___x_1977_);
lean_dec(v_a_1975_);
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_inst_1964_);
lean_dec_ref(v_prop_1963_);
lean_dec_ref(v_g_1962_);
v_a_2007_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1987_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1987_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
uint8_t v___x_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_1977_);
lean_dec(v_a_1975_);
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_prop_1963_);
lean_dec_ref(v_g_1962_);
v___x_2015_ = 0;
v___x_2016_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1964_, v___x_1986_, v___x_2015_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
return v___x_2016_;
}
v___jp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = l_Lean_mkAppB(v_g_1962_, v_a_1975_, v___y_1980_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1981_);
v___x_1983_ = v___x_1977_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_inst_1964_);
lean_dec_ref(v_prop_1963_);
lean_dec_ref(v_g_1962_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2018_, lean_object* v_prop_2019_, lean_object* v_h_2020_, lean_object* v_e_2021_, uint8_t v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
if (v_a_2022_ == 0)
{
lean_object* v___x_2030_; lean_object* v_canon_2031_; lean_object* v_cache_2032_; lean_object* v___x_2033_; 
v___x_2030_ = lean_st_ref_get(v_a_2024_);
v_canon_2031_ = lean_ctor_get(v___x_2030_, 9);
lean_inc_ref(v_canon_2031_);
lean_dec(v___x_2030_);
v_cache_2032_ = lean_ctor_get(v_canon_2031_, 0);
lean_inc_ref(v_cache_2032_);
lean_dec_ref(v_canon_2031_);
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2032_, v_e_2021_);
lean_dec_ref(v_cache_2032_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_e_2021_);
lean_dec_ref(v_h_2020_);
lean_dec_ref(v_prop_2019_);
lean_dec_ref(v_g_2018_);
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
lean_inc_ref(v_e_2021_);
v___x_2042_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2018_, v_prop_2019_, v_h_2020_, v_e_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
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
v___x_2047_ = lean_st_ref_take(v_a_2024_);
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
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2063_, v_e_2021_, v_a_2043_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_cacheInType_2064_);
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
v___x_2073_ = lean_st_ref_put(v_a_2024_, v___x_2072_);
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
lean_dec_ref(v_e_2021_);
return v___x_2042_;
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v_canon_2083_; lean_object* v_cacheInType_2084_; lean_object* v___x_2085_; 
v___x_2082_ = lean_st_ref_get(v_a_2024_);
v_canon_2083_ = lean_ctor_get(v___x_2082_, 9);
lean_inc_ref(v_canon_2083_);
lean_dec(v___x_2082_);
v_cacheInType_2084_ = lean_ctor_get(v_canon_2083_, 1);
lean_inc_ref(v_cacheInType_2084_);
lean_dec_ref(v_canon_2083_);
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2084_, v_e_2021_);
lean_dec_ref(v_cacheInType_2084_);
if (lean_obj_tag(v___x_2085_) == 1)
{
lean_object* v_val_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_e_2021_);
lean_dec_ref(v_h_2020_);
lean_dec_ref(v_prop_2019_);
lean_dec_ref(v_g_2018_);
v_val_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_val_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 0);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_val_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
lean_object* v___x_2094_; 
lean_dec(v___x_2085_);
lean_inc_ref(v_e_2021_);
v___x_2094_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2018_, v_prop_2019_, v_h_2020_, v_e_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2133_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2133_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2133_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v_canon_2100_; lean_object* v_share_2101_; lean_object* v_maxFVar_2102_; lean_object* v_proofInstInfo_2103_; lean_object* v_inferType_2104_; lean_object* v_getLevel_2105_; lean_object* v_congrInfo_2106_; lean_object* v_defEqI_2107_; lean_object* v_extensions_2108_; lean_object* v_issues_2109_; lean_object* v_instanceOverrides_2110_; uint8_t v_debug_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2132_; 
v___x_2099_ = lean_st_ref_take(v_a_2024_);
v_canon_2100_ = lean_ctor_get(v___x_2099_, 9);
v_share_2101_ = lean_ctor_get(v___x_2099_, 0);
v_maxFVar_2102_ = lean_ctor_get(v___x_2099_, 1);
v_proofInstInfo_2103_ = lean_ctor_get(v___x_2099_, 2);
v_inferType_2104_ = lean_ctor_get(v___x_2099_, 3);
v_getLevel_2105_ = lean_ctor_get(v___x_2099_, 4);
v_congrInfo_2106_ = lean_ctor_get(v___x_2099_, 5);
v_defEqI_2107_ = lean_ctor_get(v___x_2099_, 6);
v_extensions_2108_ = lean_ctor_get(v___x_2099_, 7);
v_issues_2109_ = lean_ctor_get(v___x_2099_, 8);
v_instanceOverrides_2110_ = lean_ctor_get(v___x_2099_, 10);
v_debug_2111_ = lean_ctor_get_uint8(v___x_2099_, sizeof(void*)*11);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2113_ = v___x_2099_;
v_isShared_2114_ = v_isSharedCheck_2132_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_instanceOverrides_2110_);
lean_inc(v_canon_2100_);
lean_inc(v_issues_2109_);
lean_inc(v_extensions_2108_);
lean_inc(v_defEqI_2107_);
lean_inc(v_congrInfo_2106_);
lean_inc(v_getLevel_2105_);
lean_inc(v_inferType_2104_);
lean_inc(v_proofInstInfo_2103_);
lean_inc(v_maxFVar_2102_);
lean_inc(v_share_2101_);
lean_dec(v___x_2099_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2132_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_cache_2115_; lean_object* v_cacheInType_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2131_; 
v_cache_2115_ = lean_ctor_get(v_canon_2100_, 0);
v_cacheInType_2116_ = lean_ctor_get(v_canon_2100_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_canon_2100_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2118_ = v_canon_2100_;
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_cacheInType_2116_);
lean_inc(v_cache_2115_);
lean_dec(v_canon_2100_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_inc(v_a_2095_);
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2116_, v_e_2021_, v_a_2095_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_cache_2115_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 9, v___x_2122_);
v___x_2124_ = v___x_2113_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_share_2101_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_maxFVar_2102_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_proofInstInfo_2103_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_inferType_2104_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_getLevel_2105_);
lean_ctor_set(v_reuseFailAlloc_2129_, 5, v_congrInfo_2106_);
lean_ctor_set(v_reuseFailAlloc_2129_, 6, v_defEqI_2107_);
lean_ctor_set(v_reuseFailAlloc_2129_, 7, v_extensions_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 8, v_issues_2109_);
lean_ctor_set(v_reuseFailAlloc_2129_, 9, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 10, v_instanceOverrides_2110_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*11, v_debug_2111_);
v___x_2124_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = lean_st_ref_put(v_a_2024_, v___x_2124_);
if (v_isShared_2098_ == 0)
{
v___x_2127_ = v___x_2097_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2095_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2021_);
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2134_, lean_object* v_prop_2135_, lean_object* v_h_2136_, lean_object* v_e_2137_, uint8_t v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_a_2147_; lean_object* v___y_2181_; 
if (v_a_2138_ == 0)
{
lean_object* v___x_2221_; lean_object* v_canon_2222_; lean_object* v_cache_2223_; lean_object* v___x_2224_; 
v___x_2221_ = lean_st_ref_get(v_a_2140_);
v_canon_2222_ = lean_ctor_get(v___x_2221_, 9);
lean_inc_ref(v_canon_2222_);
lean_dec(v___x_2221_);
v_cache_2223_ = lean_ctor_get(v_canon_2222_, 0);
lean_inc_ref(v_cache_2223_);
lean_dec_ref(v_canon_2222_);
v___x_2224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2223_, v_e_2137_);
lean_dec_ref(v_cache_2223_);
if (lean_obj_tag(v___x_2224_) == 1)
{
lean_object* v_val_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_e_2137_);
lean_dec_ref(v_h_2136_);
lean_dec_ref(v_prop_2135_);
lean_dec_ref(v_g_2134_);
v_val_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_val_2225_);
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
lean_ctor_set_tag(v___x_2227_, 0);
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_val_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
else
{
lean_object* v___x_2233_; 
lean_dec(v___x_2224_);
lean_inc_ref(v_prop_2135_);
v___x_2233_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2135_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_n(v_a_2234_, 2);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2234_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___y_2238_; lean_object* v___y_2241_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_inc_ref(v_h_2136_);
v___y_2241_ = v_h_2136_;
goto v___jp_2240_;
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v_a_2236_, 1);
v___y_2241_ = v_val_2248_;
goto v___jp_2240_;
}
v___jp_2237_:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_mkAppB(v_g_2134_, v_a_2234_, v___y_2238_);
v_a_2147_ = v___x_2239_;
goto v___jp_2146_;
}
v___jp_2240_:
{
size_t v___x_2242_; size_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2242_ = lean_ptr_addr(v_prop_2135_);
lean_dec_ref(v_prop_2135_);
v___x_2243_ = lean_ptr_addr(v_a_2234_);
v___x_2244_ = lean_usize_dec_eq(v___x_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec_ref(v_h_2136_);
v___y_2238_ = v___y_2241_;
goto v___jp_2237_;
}
else
{
size_t v___x_2245_; size_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2245_ = lean_ptr_addr(v_h_2136_);
lean_dec_ref(v_h_2136_);
v___x_2246_ = lean_ptr_addr(v___y_2241_);
v___x_2247_ = lean_usize_dec_eq(v___x_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
v___y_2238_ = v___y_2241_;
goto v___jp_2237_;
}
else
{
lean_dec_ref(v___y_2241_);
lean_dec(v_a_2234_);
lean_dec_ref(v_g_2134_);
lean_inc_ref(v_e_2137_);
v_a_2147_ = v_e_2137_;
goto v___jp_2146_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_e_2137_);
lean_dec_ref(v_h_2136_);
lean_dec_ref(v_prop_2135_);
lean_dec_ref(v_g_2134_);
v_a_2249_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2235_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2235_);
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
lean_dec_ref(v_h_2136_);
lean_dec_ref(v_prop_2135_);
lean_dec_ref(v_g_2134_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2233_, 1);
v_a_2147_ = v_a_2257_;
goto v___jp_2146_;
}
else
{
lean_dec_ref(v_e_2137_);
return v___x_2233_;
}
}
}
}
else
{
lean_object* v___x_2258_; lean_object* v_canon_2259_; lean_object* v_cacheInType_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v_g_2134_);
v___x_2258_ = lean_st_ref_get(v_a_2140_);
v_canon_2259_ = lean_ctor_get(v___x_2258_, 9);
lean_inc_ref(v_canon_2259_);
lean_dec(v___x_2258_);
v_cacheInType_2260_ = lean_ctor_get(v_canon_2259_, 1);
lean_inc_ref(v_cacheInType_2260_);
lean_dec_ref(v_canon_2259_);
v___x_2261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2260_, v_e_2137_);
lean_dec_ref(v_cacheInType_2260_);
if (lean_obj_tag(v___x_2261_) == 1)
{
lean_object* v_val_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_e_2137_);
lean_dec_ref(v_h_2136_);
lean_dec_ref(v_prop_2135_);
v_val_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_val_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 0);
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_val_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
else
{
lean_object* v___x_2270_; 
lean_dec(v___x_2261_);
v___x_2270_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2135_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = 0;
v___x_2273_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2136_, v_a_2271_, v___x_2272_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
v___y_2181_ = v___x_2273_;
goto v___jp_2180_;
}
else
{
lean_dec_ref(v_h_2136_);
v___y_2181_ = v___x_2270_;
goto v___jp_2180_;
}
}
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v_canon_2149_; lean_object* v_share_2150_; lean_object* v_maxFVar_2151_; lean_object* v_proofInstInfo_2152_; lean_object* v_inferType_2153_; lean_object* v_getLevel_2154_; lean_object* v_congrInfo_2155_; lean_object* v_defEqI_2156_; lean_object* v_extensions_2157_; lean_object* v_issues_2158_; lean_object* v_instanceOverrides_2159_; uint8_t v_debug_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2179_; 
v___x_2148_ = lean_st_ref_take(v_a_2140_);
v_canon_2149_ = lean_ctor_get(v___x_2148_, 9);
v_share_2150_ = lean_ctor_get(v___x_2148_, 0);
v_maxFVar_2151_ = lean_ctor_get(v___x_2148_, 1);
v_proofInstInfo_2152_ = lean_ctor_get(v___x_2148_, 2);
v_inferType_2153_ = lean_ctor_get(v___x_2148_, 3);
v_getLevel_2154_ = lean_ctor_get(v___x_2148_, 4);
v_congrInfo_2155_ = lean_ctor_get(v___x_2148_, 5);
v_defEqI_2156_ = lean_ctor_get(v___x_2148_, 6);
v_extensions_2157_ = lean_ctor_get(v___x_2148_, 7);
v_issues_2158_ = lean_ctor_get(v___x_2148_, 8);
v_instanceOverrides_2159_ = lean_ctor_get(v___x_2148_, 10);
v_debug_2160_ = lean_ctor_get_uint8(v___x_2148_, sizeof(void*)*11);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2162_ = v___x_2148_;
v_isShared_2163_ = v_isSharedCheck_2179_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_instanceOverrides_2159_);
lean_inc(v_canon_2149_);
lean_inc(v_issues_2158_);
lean_inc(v_extensions_2157_);
lean_inc(v_defEqI_2156_);
lean_inc(v_congrInfo_2155_);
lean_inc(v_getLevel_2154_);
lean_inc(v_inferType_2153_);
lean_inc(v_proofInstInfo_2152_);
lean_inc(v_maxFVar_2151_);
lean_inc(v_share_2150_);
lean_dec(v___x_2148_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2179_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_cache_2164_; lean_object* v_cacheInType_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2178_; 
v_cache_2164_ = lean_ctor_get(v_canon_2149_, 0);
v_cacheInType_2165_ = lean_ctor_get(v_canon_2149_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_canon_2149_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2167_ = v_canon_2149_;
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_cacheInType_2165_);
lean_inc(v_cache_2164_);
lean_dec(v_canon_2149_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_inc_ref(v_a_2147_);
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2164_, v_e_2137_, v_a_2147_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_cacheInType_2165_);
v___x_2171_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 9, v___x_2171_);
v___x_2173_ = v___x_2162_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_share_2150_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_maxFVar_2151_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_proofInstInfo_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_inferType_2153_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_getLevel_2154_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_congrInfo_2155_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_defEqI_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_extensions_2157_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_issues_2158_);
lean_ctor_set(v_reuseFailAlloc_2176_, 9, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2176_, 10, v_instanceOverrides_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*11, v_debug_2160_);
v___x_2173_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_st_ref_put(v_a_2140_, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_a_2147_);
return v___x_2175_;
}
}
}
}
}
v___jp_2180_:
{
if (lean_obj_tag(v___y_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2220_; 
v_a_2182_ = lean_ctor_get(v___y_2181_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___y_2181_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2184_ = v___y_2181_;
v_isShared_2185_ = v_isSharedCheck_2220_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___y_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2220_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v_canon_2187_; lean_object* v_share_2188_; lean_object* v_maxFVar_2189_; lean_object* v_proofInstInfo_2190_; lean_object* v_inferType_2191_; lean_object* v_getLevel_2192_; lean_object* v_congrInfo_2193_; lean_object* v_defEqI_2194_; lean_object* v_extensions_2195_; lean_object* v_issues_2196_; lean_object* v_instanceOverrides_2197_; uint8_t v_debug_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2219_; 
v___x_2186_ = lean_st_ref_take(v_a_2140_);
v_canon_2187_ = lean_ctor_get(v___x_2186_, 9);
v_share_2188_ = lean_ctor_get(v___x_2186_, 0);
v_maxFVar_2189_ = lean_ctor_get(v___x_2186_, 1);
v_proofInstInfo_2190_ = lean_ctor_get(v___x_2186_, 2);
v_inferType_2191_ = lean_ctor_get(v___x_2186_, 3);
v_getLevel_2192_ = lean_ctor_get(v___x_2186_, 4);
v_congrInfo_2193_ = lean_ctor_get(v___x_2186_, 5);
v_defEqI_2194_ = lean_ctor_get(v___x_2186_, 6);
v_extensions_2195_ = lean_ctor_get(v___x_2186_, 7);
v_issues_2196_ = lean_ctor_get(v___x_2186_, 8);
v_instanceOverrides_2197_ = lean_ctor_get(v___x_2186_, 10);
v_debug_2198_ = lean_ctor_get_uint8(v___x_2186_, sizeof(void*)*11);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2200_ = v___x_2186_;
v_isShared_2201_ = v_isSharedCheck_2219_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_instanceOverrides_2197_);
lean_inc(v_canon_2187_);
lean_inc(v_issues_2196_);
lean_inc(v_extensions_2195_);
lean_inc(v_defEqI_2194_);
lean_inc(v_congrInfo_2193_);
lean_inc(v_getLevel_2192_);
lean_inc(v_inferType_2191_);
lean_inc(v_proofInstInfo_2190_);
lean_inc(v_maxFVar_2189_);
lean_inc(v_share_2188_);
lean_dec(v___x_2186_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2219_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_cache_2202_; lean_object* v_cacheInType_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2218_; 
v_cache_2202_ = lean_ctor_get(v_canon_2187_, 0);
v_cacheInType_2203_ = lean_ctor_get(v_canon_2187_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_canon_2187_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2205_ = v_canon_2187_;
v_isShared_2206_ = v_isSharedCheck_2218_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_cacheInType_2203_);
lean_inc(v_cache_2202_);
lean_dec(v_canon_2187_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2218_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
lean_inc(v_a_2182_);
v___x_2207_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2203_, v_e_2137_, v_a_2182_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_cache_2202_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 9, v___x_2209_);
v___x_2211_ = v___x_2200_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_share_2188_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_maxFVar_2189_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_proofInstInfo_2190_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_inferType_2191_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v_getLevel_2192_);
lean_ctor_set(v_reuseFailAlloc_2216_, 5, v_congrInfo_2193_);
lean_ctor_set(v_reuseFailAlloc_2216_, 6, v_defEqI_2194_);
lean_ctor_set(v_reuseFailAlloc_2216_, 7, v_extensions_2195_);
lean_ctor_set(v_reuseFailAlloc_2216_, 8, v_issues_2196_);
lean_ctor_set(v_reuseFailAlloc_2216_, 9, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2216_, 10, v_instanceOverrides_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2216_, sizeof(void*)*11, v_debug_2198_);
v___x_2211_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_st_ref_put(v_a_2140_, v___x_2211_);
if (v_isShared_2185_ == 0)
{
v___x_2214_ = v___x_2184_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2182_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2137_);
return v___y_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2274_, lean_object* v_snd_2275_, lean_object* v_a_2276_, uint8_t v___x_2277_, lean_object* v_fst_2278_, lean_object* v___x_2279_, lean_object* v_____r_2280_, uint8_t v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_arg_x27_2290_; lean_object* v___x_2324_; 
lean_inc_ref(v___x_2274_);
v___x_2324_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2279_, v_a_2276_, v___x_2274_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
switch(v___x_2326_)
{
case 0:
{
lean_object* v___x_2327_; 
lean_inc_ref(v___x_2274_);
v___x_2327_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2274_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v_arg_x27_2290_ = v_a_2328_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2329_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2327_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
case 1:
{
lean_object* v___x_2337_; 
lean_inc_ref(v___x_2274_);
v___x_2337_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2274_, v___y_2285_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_Expr_cleanupAnnotations(v_a_2338_);
v___x_2340_ = l_Lean_Expr_isApp(v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2339_);
goto v___jp_2313_;
}
else
{
lean_object* v_arg_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_arg_2341_ = lean_ctor_get(v___x_2339_, 1);
lean_inc_ref(v_arg_2341_);
v___x_2342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2339_);
v___x_2343_ = l_Lean_Expr_isApp(v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
goto v___jp_2313_;
}
else
{
lean_object* v_arg_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_arg_2344_ = lean_ctor_get(v___x_2342_, 1);
lean_inc_ref(v_arg_2344_);
v___x_2345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2342_);
v___x_2346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2347_ = l_Lean_Expr_isConstOf(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2349_ = l_Lean_Expr_isConstOf(v___x_2345_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v___x_2345_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_arg_2341_);
goto v___jp_2313_;
}
else
{
lean_object* v___x_2350_; 
lean_inc_ref(v___x_2274_);
v___x_2350_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2345_, v_arg_2344_, v_arg_2341_, v___x_2274_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v_arg_x27_2290_ = v_a_2351_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2352_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2350_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
else
{
lean_object* v___x_2360_; 
lean_inc_ref(v___x_2274_);
v___x_2360_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2345_, v_arg_2344_, v_arg_2341_, v___x_2274_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v_arg_x27_2290_ = v_a_2361_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2362_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2370_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2337_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2337_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
default: 
{
goto v___jp_2302_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2378_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2324_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2324_);
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
v___jp_2289_:
{
size_t v___x_2291_; size_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2291_ = lean_ptr_addr(v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2292_ = lean_ptr_addr(v_arg_x27_2290_);
v___x_2293_ = lean_usize_dec_eq(v___x_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec(v_fst_2278_);
v___x_2294_ = lean_array_fset(v_snd_2275_, v_a_2276_, v_arg_x27_2290_);
v___x_2295_ = lean_box(v___x_2277_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___x_2294_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_arg_x27_2290_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_fst_2278_);
lean_ctor_set(v___x_2299_, 1, v_snd_2275_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
v___jp_2302_:
{
lean_object* v___x_2303_; 
lean_inc_ref(v___x_2274_);
v___x_2303_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2274_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v_arg_x27_2290_ = v_a_2304_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2305_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2303_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2303_);
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
v___jp_2313_:
{
lean_object* v___x_2314_; 
lean_inc_ref(v___x_2274_);
v___x_2314_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2274_, v___x_2277_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v_arg_x27_2290_ = v_a_2315_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_fst_2278_);
lean_dec(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v_a_2316_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2314_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2390_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2391_ = l_Lean_Name_append(v___x_2390_, v___x_2389_);
return v___x_2391_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2400_ = l_Lean_stringToMessageData(v___x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_, uint8_t v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___y_2414_; uint8_t v___x_2436_; 
v___x_2436_ = lean_nat_dec_lt(v_a_2403_, v_upperBound_2401_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_dec(v_a_2403_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v_b_2404_);
return v___x_2437_;
}
else
{
lean_object* v_toCold_2438_; lean_object* v_options_2439_; lean_object* v_fst_2440_; lean_object* v_snd_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2505_; 
v_toCold_2438_ = lean_ctor_get(v___y_2410_, 0);
v_options_2439_ = lean_ctor_get(v_toCold_2438_, 2);
v_fst_2440_ = lean_ctor_get(v_b_2404_, 0);
v_snd_2441_ = lean_ctor_get(v_b_2404_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_b_2404_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2443_ = v_b_2404_;
v_isShared_2444_ = v_isSharedCheck_2505_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_snd_2441_);
lean_inc(v_fst_2440_);
lean_dec(v_b_2404_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2505_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v_inheritedTraceOptions_2445_; uint8_t v_hasTrace_2446_; lean_object* v___x_2447_; 
v_inheritedTraceOptions_2445_ = lean_ctor_get(v_toCold_2438_, 11);
v_hasTrace_2446_ = lean_ctor_get_uint8(v_options_2439_, sizeof(void*)*1);
v___x_2447_ = lean_array_fget(v_snd_2441_, v_a_2403_);
if (v_hasTrace_2446_ == 0)
{
lean_del_object(v___x_2443_);
goto v___jp_2448_;
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2452_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2445_, v_options_2439_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_del_object(v___x_2443_);
goto v___jp_2448_;
}
else
{
lean_object* v___x_2454_; 
lean_inc(v___x_2447_);
v___x_2454_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2402_, v_a_2403_, v___x_2447_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
lean_inc(v___x_2447_);
v___x_2456_ = lean_infer_type(v___x_2447_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; lean_object* v___y_2460_; uint8_t v___x_2484_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2484_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
switch(v___x_2484_)
{
case 0:
{
lean_object* v___x_2485_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2460_ = v___x_2485_;
goto v___jp_2459_;
}
case 1:
{
lean_object* v___x_2486_; 
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2460_ = v___x_2486_;
goto v___jp_2459_;
}
case 2:
{
lean_object* v___x_2487_; 
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2460_ = v___x_2487_;
goto v___jp_2459_;
}
default: 
{
lean_object* v___x_2488_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2460_ = v___x_2488_;
goto v___jp_2459_;
}
}
v___jp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_inc(v___y_2460_);
v___x_2461_ = l_Lean_MessageData_ofFormat(v___y_2460_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set_tag(v___x_2443_, 7);
lean_ctor_set(v___x_2443_, 1, v___x_2461_);
lean_ctor_set(v___x_2443_, 0, v___x_2458_);
v___x_2463_ = v___x_2443_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2464_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc(v___x_2447_);
v___x_2466_ = l_Lean_MessageData_ofExpr(v___x_2447_);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_MessageData_ofExpr(v_a_2457_);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2451_, v___x_2471_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2447_, v_snd_2441_, v_a_2403_, v___x_2436_, v_fst_2440_, v___x_2402_, v_a_2473_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
v___y_2414_ = v___x_2474_;
goto v___jp_2413_;
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v___x_2447_);
lean_dec(v_snd_2441_);
lean_dec(v_fst_2440_);
lean_dec(v_a_2403_);
v_a_2475_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2472_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2472_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_a_2455_);
lean_dec(v___x_2447_);
lean_del_object(v___x_2443_);
lean_dec(v_snd_2441_);
lean_dec(v_fst_2440_);
lean_dec(v_a_2403_);
v_a_2489_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2456_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2456_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v___x_2447_);
lean_del_object(v___x_2443_);
lean_dec(v_snd_2441_);
lean_dec(v_fst_2440_);
lean_dec(v_a_2403_);
v_a_2497_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2454_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2454_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_box(0);
v___x_2450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2447_, v_snd_2441_, v_a_2403_, v___x_2436_, v_fst_2440_, v___x_2402_, v___x_2449_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
v___y_2414_ = v___x_2450_;
goto v___jp_2413_;
}
}
}
v___jp_2413_:
{
if (lean_obj_tag(v___y_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2427_; 
v_a_2415_ = lean_ctor_get(v___y_2414_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___y_2414_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2417_ = v___y_2414_;
v_isShared_2418_ = v_isSharedCheck_2427_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___y_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2427_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
if (lean_obj_tag(v_a_2415_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; 
lean_dec(v_a_2403_);
v_a_2419_ = lean_ctor_get(v_a_2415_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v_a_2415_, 1);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v_a_2419_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_del_object(v___x_2417_);
v_a_2423_ = lean_ctor_get(v_a_2415_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v_a_2415_, 1);
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_nat_add(v_a_2403_, v___x_2424_);
lean_dec(v_a_2403_);
v_a_2403_ = v___x_2425_;
v_b_2404_ = v_a_2423_;
goto _start;
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2403_);
v_a_2428_ = lean_ctor_get(v___y_2414_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___y_2414_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___y_2414_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___y_2414_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2506_, lean_object* v_x_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_, uint8_t v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___y_2519_; uint8_t v_modified_2520_; lean_object* v_f_2521_; uint8_t v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v_args_2577_; uint8_t v_modified_2578_; uint8_t v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; 
if (lean_obj_tag(v_x_2507_) == 5)
{
lean_object* v_fn_2614_; lean_object* v_arg_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_fn_2614_ = lean_ctor_get(v_x_2507_, 0);
lean_inc_ref(v_fn_2614_);
v_arg_2615_ = lean_ctor_get(v_x_2507_, 1);
lean_inc_ref(v_arg_2615_);
lean_dec_ref_known(v_x_2507_, 2);
v___x_2616_ = lean_array_set(v_x_2508_, v_x_2509_, v_arg_2615_);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_sub(v_x_2509_, v___x_2617_);
lean_dec(v_x_2509_);
v_x_2507_ = v_fn_2614_;
v_x_2508_ = v___x_2616_;
v_x_2509_ = v___x_2618_;
goto _start;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_dec(v_x_2509_);
v___x_2620_ = lean_array_get_size(v_x_2508_);
v___x_2621_ = lean_unsigned_to_nat(2u);
v___x_2622_ = lean_nat_dec_eq(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
v___y_2593_ = v___y_2510_;
v___y_2594_ = v___y_2511_;
v___y_2595_ = v___y_2512_;
v___y_2596_ = v___y_2513_;
v___y_2597_ = v___y_2514_;
v___y_2598_ = v___y_2515_;
v___y_2599_ = v___y_2516_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = l_Lean_instInhabitedExpr;
v___x_2624_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2625_ = l_Lean_Expr_isConstOf(v_x_2507_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2627_ = l_Lean_Expr_isConstOf(v_x_2507_, v___x_2626_);
if (v___x_2627_ == 0)
{
v___y_2593_ = v___y_2510_;
v___y_2594_ = v___y_2511_;
v___y_2595_ = v___y_2512_;
v___y_2596_ = v___y_2513_;
v___y_2597_ = v___y_2514_;
v___y_2598_ = v___y_2515_;
v___y_2599_ = v___y_2516_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_array_get(v___x_2623_, v_x_2508_, v___x_2628_);
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_array_get(v___x_2623_, v_x_2508_, v___x_2630_);
lean_dec_ref(v_x_2508_);
v___x_2632_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2507_, v___x_2629_, v___x_2631_, v_e_2506_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2632_;
}
}
else
{
lean_object* v___x_2633_; lean_object* v_prop_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_unsigned_to_nat(0u);
v_prop_2634_ = lean_array_get_borrowed(v___x_2623_, v_x_2508_, v___x_2633_);
lean_inc(v_prop_2634_);
v___x_2635_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2634_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2652_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2652_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2652_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
size_t v___x_2640_; size_t v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = lean_ptr_addr(v_prop_2634_);
v___x_2641_ = lean_ptr_addr(v_a_2636_);
v___x_2642_ = lean_usize_dec_eq(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec_ref(v_e_2506_);
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_array_get(v___x_2623_, v_x_2508_, v___x_2643_);
lean_dec_ref(v_x_2508_);
v___x_2645_ = l_Lean_mkAppB(v_x_2507_, v_a_2636_, v___x_2644_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2645_);
v___x_2647_ = v___x_2638_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v___x_2650_; 
lean_dec(v_a_2636_);
lean_dec_ref(v_x_2508_);
lean_dec_ref(v_x_2507_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v_e_2506_);
v___x_2650_ = v___x_2638_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_e_2506_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_dec_ref(v_x_2508_);
lean_dec_ref(v_x_2507_);
lean_dec_ref(v_e_2506_);
return v___x_2635_;
}
}
}
}
v___jp_2518_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_box(0);
lean_inc_ref(v_f_2521_);
v___x_2530_ = l_Lean_Meta_getFunInfo(v_f_2521_, v___x_2529_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_paramInfo_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2566_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v_paramInfo_2532_ = lean_ctor_get(v_a_2531_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_a_2531_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v_a_2531_, 1);
lean_dec(v_unused_2567_);
v___x_2534_ = v_a_2531_;
v_isShared_2535_ = v_isSharedCheck_2566_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_paramInfo_2532_);
lean_dec(v_a_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2566_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2536_ = lean_array_get_size(v___y_2519_);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_box(v_modified_2520_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___y_2519_);
lean_ctor_set(v___x_2534_, 0, v___x_2538_);
v___x_2540_ = v___x_2534_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v___y_2519_);
v___x_2540_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2536_, v_paramInfo_2532_, v___x_2537_, v___x_2540_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec_ref(v_paramInfo_2532_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2556_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2556_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2556_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_fst_2546_; uint8_t v___x_2547_; 
v_fst_2546_ = lean_ctor_get(v_a_2542_, 0);
v___x_2547_ = lean_unbox(v_fst_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2549_; 
lean_dec(v_a_2542_);
lean_dec_ref(v_f_2521_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_e_2506_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_e_2506_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
else
{
lean_object* v_snd_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_dec_ref(v_e_2506_);
v_snd_2551_ = lean_ctor_get(v_a_2542_, 1);
lean_inc(v_snd_2551_);
lean_dec(v_a_2542_);
v___x_2552_ = l_Lean_mkAppN(v_f_2521_, v_snd_2551_);
lean_dec(v_snd_2551_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2552_);
v___x_2554_ = v___x_2544_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_f_2521_);
lean_dec_ref(v_e_2506_);
v_a_2557_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2541_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2541_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v_f_2521_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_e_2506_);
v_a_2568_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2530_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2530_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
v___jp_2576_:
{
lean_object* v___x_2586_; 
lean_inc_ref(v_x_2507_);
v___x_2586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2507_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; size_t v___x_2588_; size_t v___x_2589_; uint8_t v___x_2590_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = lean_ptr_addr(v_x_2507_);
v___x_2589_ = lean_ptr_addr(v_a_2587_);
v___x_2590_ = lean_usize_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
lean_dec_ref(v_x_2507_);
v___x_2591_ = 1;
v___y_2519_ = v_args_2577_;
v_modified_2520_ = v___x_2591_;
v_f_2521_ = v_a_2587_;
v___y_2522_ = v___y_2579_;
v___y_2523_ = v___y_2580_;
v___y_2524_ = v___y_2581_;
v___y_2525_ = v___y_2582_;
v___y_2526_ = v___y_2583_;
v___y_2527_ = v___y_2584_;
v___y_2528_ = v___y_2585_;
goto v___jp_2518_;
}
else
{
lean_dec(v_a_2587_);
v___y_2519_ = v_args_2577_;
v_modified_2520_ = v_modified_2578_;
v_f_2521_ = v_x_2507_;
v___y_2522_ = v___y_2579_;
v___y_2523_ = v___y_2580_;
v___y_2524_ = v___y_2581_;
v___y_2525_ = v___y_2582_;
v___y_2526_ = v___y_2583_;
v___y_2527_ = v___y_2584_;
v___y_2528_ = v___y_2585_;
goto v___jp_2518_;
}
}
else
{
lean_dec_ref(v_args_2577_);
lean_dec_ref(v_x_2507_);
lean_dec_ref(v_e_2506_);
return v___x_2586_;
}
}
v___jp_2592_:
{
uint8_t v_modified_2600_; lean_object* v___x_2601_; uint8_t v_modified_2602_; 
v_modified_2600_ = 0;
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2602_ = l_Lean_Expr_isConstOf(v_x_2507_, v___x_2601_);
if (v_modified_2602_ == 0)
{
v_args_2577_ = v_x_2508_;
v_modified_2578_ = v_modified_2600_;
v___y_2579_ = v___y_2593_;
v___y_2580_ = v___y_2594_;
v___y_2581_ = v___y_2595_;
v___y_2582_ = v___y_2596_;
v___y_2583_ = v___y_2597_;
v___y_2584_ = v___y_2598_;
v___y_2585_ = v___y_2599_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2603_; 
lean_inc_ref(v_x_2508_);
v___x_2603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2508_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
if (lean_obj_tag(v_a_2604_) == 1)
{
lean_object* v_val_2605_; 
lean_dec_ref(v_x_2508_);
v_val_2605_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v_a_2604_, 1);
v_args_2577_ = v_val_2605_;
v_modified_2578_ = v_modified_2602_;
v___y_2579_ = v___y_2593_;
v___y_2580_ = v___y_2594_;
v___y_2581_ = v___y_2595_;
v___y_2582_ = v___y_2596_;
v___y_2583_ = v___y_2597_;
v___y_2584_ = v___y_2598_;
v___y_2585_ = v___y_2599_;
goto v___jp_2576_;
}
else
{
lean_dec(v_a_2604_);
v_args_2577_ = v_x_2508_;
v_modified_2578_ = v_modified_2600_;
v___y_2579_ = v___y_2593_;
v___y_2580_ = v___y_2594_;
v___y_2581_ = v___y_2595_;
v___y_2582_ = v___y_2596_;
v___y_2583_ = v___y_2597_;
v___y_2584_ = v___y_2598_;
v___y_2585_ = v___y_2599_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_x_2508_);
lean_dec_ref(v_x_2507_);
lean_dec_ref(v_e_2506_);
v_a_2606_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2603_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2603_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2653_, uint8_t v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_dummy_2662_; lean_object* v_nargs_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_dummy_2662_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2663_ = l_Lean_Expr_getAppNumArgs(v_e_2653_);
lean_inc(v_nargs_2663_);
v___x_2664_ = lean_mk_array(v_nargs_2663_, v_dummy_2662_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_sub(v_nargs_2663_, v___x_2665_);
lean_dec(v_nargs_2663_);
lean_inc_ref(v_e_2653_);
v___x_2667_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2653_, v_e_2653_, v___x_2664_, v___x_2666_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2668_, uint8_t v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v___x_2697_; 
lean_inc_ref(v_e_2668_);
v___x_2697_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2668_);
if (v___x_2697_ == 0)
{
lean_object* v_f_2698_; 
v_f_2698_ = l_Lean_Expr_getAppFn(v_e_2668_);
if (lean_obj_tag(v_f_2698_) == 4)
{
lean_object* v_declName_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v_declName_2699_ = lean_ctor_get(v_f_2698_, 0);
lean_inc(v_declName_2699_);
lean_dec_ref_known(v_f_2698_, 2);
v___x_2700_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2701_ = lean_name_eq(v_declName_2699_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_2703_ = lean_name_eq(v_declName_2699_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2705_ = lean_name_eq(v_declName_2699_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2707_ = lean_name_eq(v_declName_2699_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_2709_ = lean_name_eq(v_declName_2699_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2699_, v_a_2675_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2740_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2740_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2740_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
if (lean_obj_tag(v_a_2711_) == 1)
{
lean_object* v_val_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2713_);
v_val_2715_ = lean_ctor_get(v_a_2711_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v_a_2711_, 1);
lean_inc_ref(v_e_2668_);
v___x_2716_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2715_, v_e_2668_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec(v_val_2715_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2728_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
if (lean_obj_tag(v_a_2717_) == 0)
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_e_2668_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_e_2668_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
else
{
lean_object* v_val_2724_; lean_object* v___x_2726_; 
lean_dec_ref(v_e_2668_);
v_val_2724_ = lean_ctor_get(v_a_2717_, 0);
lean_inc(v_val_2724_);
lean_dec_ref_known(v_a_2717_, 1);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_val_2724_);
v___x_2726_ = v___x_2719_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_val_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_e_2668_);
v_a_2729_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2716_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2716_);
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
else
{
lean_object* v___x_2738_; 
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_e_2668_);
v___x_2738_ = v___x_2713_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_e_2668_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_e_2668_);
v_a_2741_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2710_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2710_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_dec(v_declName_2699_);
goto v___jp_2677_;
}
}
else
{
lean_dec(v_declName_2699_);
goto v___jp_2677_;
}
}
else
{
lean_dec(v_declName_2699_);
goto v___jp_2677_;
}
}
else
{
lean_dec(v_declName_2699_);
goto v___jp_2677_;
}
}
else
{
lean_dec(v_declName_2699_);
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2749_; 
lean_dec_ref(v_f_2698_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_e_2668_);
return v___x_2749_;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_inc_ref(v_e_2668_);
v___x_2750_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2750_, 0, v_e_2668_);
v___x_2751_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2750_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2785_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2785_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2785_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
if (lean_obj_tag(v_a_2752_) == 1)
{
lean_object* v_val_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec_ref(v_e_2668_);
v_val_2756_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v_a_2752_, 1);
v___x_2757_ = l_Lean_mkNatLit(v_val_2756_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2757_);
v___x_2759_ = v___x_2754_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; 
lean_del_object(v___x_2754_);
lean_dec(v_a_2752_);
lean_inc_ref(v_e_2668_);
v___x_2761_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2668_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2776_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2776_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2776_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
if (lean_obj_tag(v_a_2762_) == 1)
{
lean_object* v_val_2766_; lean_object* v_fst_2767_; lean_object* v_snd_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_dec_ref(v_e_2668_);
v_val_2766_ = lean_ctor_get(v_a_2762_, 0);
lean_inc(v_val_2766_);
lean_dec_ref_known(v_a_2762_, 1);
v_fst_2767_ = lean_ctor_get(v_val_2766_, 0);
lean_inc(v_fst_2767_);
v_snd_2768_ = lean_ctor_get(v_val_2766_, 1);
lean_inc(v_snd_2768_);
lean_dec(v_val_2766_);
v___x_2769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2767_, v_snd_2768_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2769_);
v___x_2771_ = v___x_2764_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v___x_2774_; 
lean_dec(v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_e_2668_);
v___x_2774_ = v___x_2764_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_e_2668_);
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
lean_dec_ref(v_e_2668_);
v_a_2777_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2761_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2761_);
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
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_e_2668_);
v_a_2786_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2751_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2751_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
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
v___jp_2677_:
{
lean_object* v___x_2678_; 
lean_inc_ref(v_e_2668_);
v___x_2678_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2668_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2688_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
if (lean_obj_tag(v_a_2679_) == 1)
{
lean_object* v_val_2683_; lean_object* v___x_2684_; 
lean_del_object(v___x_2681_);
lean_dec_ref(v_e_2668_);
v_val_2683_ = lean_ctor_get(v_a_2679_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v_a_2679_, 1);
v___x_2684_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2683_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2684_;
}
else
{
lean_object* v___x_2686_; 
lean_dec(v_a_2679_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_e_2668_);
v___x_2686_ = v___x_2681_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_e_2668_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v_e_2668_);
v_a_2689_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2678_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2678_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2794_, uint8_t v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2804_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
return v___x_2805_;
}
else
{
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2806_, uint8_t v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2806_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
if (lean_obj_tag(v_a_2816_) == 0)
{
lean_object* v_val_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_e_2806_);
v_val_2817_ = lean_ctor_get(v_a_2816_, 0);
lean_inc_ref(v_val_2817_);
lean_dec_ref_known(v_a_2816_, 1);
v___x_2818_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2817_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; 
lean_dec(v_a_2816_);
v___x_2819_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2820_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2831_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
if (lean_obj_tag(v_a_2822_) == 0)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; 
lean_del_object(v___x_2824_);
lean_dec(v_a_2820_);
v_val_2826_ = lean_ctor_get(v_a_2822_, 0);
lean_inc_ref(v_val_2826_);
lean_dec_ref_known(v_a_2822_, 1);
v___x_2827_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2826_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
return v___x_2827_;
}
else
{
lean_object* v___x_2829_; 
lean_dec(v_a_2822_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v_a_2820_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2820_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2820_);
v_a_2832_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2821_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2821_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
return v___x_2819_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_e_2806_);
v_a_2840_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2815_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2815_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2854_, uint8_t v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
uint8_t v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___x_2873_; 
lean_inc_ref(v_e_2854_);
v___x_2873_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2854_, v_a_2859_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_Expr_cleanupAnnotations(v_a_2874_);
v___x_2876_ = l_Lean_Expr_isApp(v___x_2875_);
if (v___x_2876_ == 0)
{
lean_dec_ref(v___x_2875_);
v___y_2864_ = v_a_2855_;
v___y_2865_ = v_a_2856_;
v___y_2866_ = v_a_2857_;
v___y_2867_ = v_a_2858_;
v___y_2868_ = v_a_2859_;
v___y_2869_ = v_a_2860_;
v___y_2870_ = v_a_2861_;
goto v___jp_2863_;
}
else
{
lean_object* v_arg_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v_arg_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc_ref(v_arg_2877_);
v___x_2878_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2875_);
v___x_2879_ = l_Lean_Expr_isApp(v___x_2878_);
if (v___x_2879_ == 0)
{
lean_dec_ref(v___x_2878_);
lean_dec_ref(v_arg_2877_);
v___y_2864_ = v_a_2855_;
v___y_2865_ = v_a_2856_;
v___y_2866_ = v_a_2857_;
v___y_2867_ = v_a_2858_;
v___y_2868_ = v_a_2859_;
v___y_2869_ = v_a_2860_;
v___y_2870_ = v_a_2861_;
goto v___jp_2863_;
}
else
{
lean_object* v_arg_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_arg_2880_ = lean_ctor_get(v___x_2878_, 1);
lean_inc_ref(v_arg_2880_);
v___x_2881_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2878_);
v___x_2882_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2883_ = l_Lean_Expr_isConstOf(v___x_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_dec_ref(v___x_2881_);
lean_dec_ref(v_arg_2880_);
lean_dec_ref(v_arg_2877_);
v___y_2864_ = v_a_2855_;
v___y_2865_ = v_a_2856_;
v___y_2866_ = v_a_2857_;
v___y_2867_ = v_a_2858_;
v___y_2868_ = v_a_2859_;
v___y_2869_ = v_a_2860_;
v___y_2870_ = v_a_2861_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2881_, v_arg_2880_, v_arg_2877_, v_e_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
return v___x_2884_;
}
}
}
}
else
{
lean_dec_ref(v_e_2854_);
return v___x_2873_;
}
v___jp_2863_:
{
uint8_t v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = 0;
v___x_2872_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2854_, v___x_2871_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2885_, lean_object* v_00_u03b1_2886_, lean_object* v_c_2887_, lean_object* v_inst_2888_, lean_object* v_a_2889_, lean_object* v_b_2890_, uint8_t v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2887_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; uint8_t v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc_n(v_a_2900_, 2);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2900_);
if (v___x_2901_ == 0)
{
uint8_t v___x_2902_; 
lean_inc(v_a_2900_);
v___x_2902_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2900_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2886_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2888_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2889_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2918_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = l_Lean_mkApp5(v_f_2885_, v_a_2904_, v_a_2900_, v_a_2906_, v_a_2908_, v_a_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2914_);
v___x_2916_ = v___x_2912_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
else
{
lean_dec(v_a_2908_);
lean_dec(v_a_2906_);
lean_dec(v_a_2904_);
lean_dec(v_a_2900_);
lean_dec_ref(v_f_2885_);
return v___x_2909_;
}
}
else
{
lean_dec(v_a_2906_);
lean_dec(v_a_2904_);
lean_dec(v_a_2900_);
lean_dec_ref(v_b_2890_);
lean_dec_ref(v_f_2885_);
return v___x_2907_;
}
}
else
{
lean_dec(v_a_2904_);
lean_dec(v_a_2900_);
lean_dec_ref(v_b_2890_);
lean_dec_ref(v_a_2889_);
lean_dec_ref(v_f_2885_);
return v___x_2905_;
}
}
else
{
lean_dec(v_a_2900_);
lean_dec_ref(v_b_2890_);
lean_dec_ref(v_a_2889_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_f_2885_);
return v___x_2903_;
}
}
else
{
lean_object* v___x_2919_; 
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2889_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_00_u03b1_2886_);
lean_dec_ref(v_f_2885_);
v___x_2919_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
return v___x_2919_;
}
}
else
{
lean_object* v___x_2920_; 
lean_dec(v_a_2900_);
lean_dec_ref(v_b_2890_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_00_u03b1_2886_);
lean_dec_ref(v_f_2885_);
v___x_2920_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2889_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
return v___x_2920_;
}
}
else
{
lean_dec_ref(v_b_2890_);
lean_dec_ref(v_a_2889_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_00_u03b1_2886_);
lean_dec_ref(v_f_2885_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2921_, lean_object* v_00_u03b1_2922_, lean_object* v_c_2923_, lean_object* v_a_2924_, lean_object* v_b_2925_, uint8_t v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2923_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; uint8_t v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_n(v_a_2935_, 2);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l_Lean_Expr_isBoolTrue(v_a_2935_);
if (v___x_2936_ == 0)
{
uint8_t v___x_2937_; 
lean_inc(v_a_2935_);
v___x_2937_ = l_Lean_Expr_isBoolFalse(v_a_2935_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
v___x_2938_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2922_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2924_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_mkApp4(v_f_2921_, v_a_2939_, v_a_2935_, v_a_2941_, v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
else
{
lean_dec(v_a_2941_);
lean_dec(v_a_2939_);
lean_dec(v_a_2935_);
lean_dec_ref(v_f_2921_);
return v___x_2942_;
}
}
else
{
lean_dec(v_a_2939_);
lean_dec(v_a_2935_);
lean_dec_ref(v_b_2925_);
lean_dec_ref(v_f_2921_);
return v___x_2940_;
}
}
else
{
lean_dec(v_a_2935_);
lean_dec_ref(v_b_2925_);
lean_dec_ref(v_a_2924_);
lean_dec_ref(v_f_2921_);
return v___x_2938_;
}
}
else
{
lean_object* v___x_2952_; 
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2924_);
lean_dec_ref(v_00_u03b1_2922_);
lean_dec_ref(v_f_2921_);
v___x_2952_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2952_;
}
}
else
{
lean_object* v___x_2953_; 
lean_dec(v_a_2935_);
lean_dec_ref(v_b_2925_);
lean_dec_ref(v_00_u03b1_2922_);
lean_dec_ref(v_f_2921_);
v___x_2953_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2924_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2953_;
}
}
else
{
lean_dec_ref(v_b_2925_);
lean_dec_ref(v_a_2924_);
lean_dec_ref(v_00_u03b1_2922_);
lean_dec_ref(v_f_2921_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2954_, uint8_t v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___y_2964_; lean_object* v___y_2965_; uint8_t v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v___y_2972_; uint8_t v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___x_3000_; 
lean_inc_ref(v_e_2954_);
v___x_3000_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2954_, v_a_2959_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = l_Lean_Expr_cleanupAnnotations(v_a_3001_);
v___x_3003_ = l_Lean_Expr_isApp(v___x_3002_);
if (v___x_3003_ == 0)
{
lean_dec_ref(v___x_3002_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_arg_3004_ = lean_ctor_get(v___x_3002_, 1);
lean_inc_ref(v_arg_3004_);
v___x_3005_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3002_);
v___x_3006_ = l_Lean_Expr_isApp(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec_ref(v_arg_3004_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_arg_3007_ = lean_ctor_get(v___x_3005_, 1);
lean_inc_ref(v_arg_3007_);
v___x_3008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3005_);
v___x_3009_ = l_Lean_Expr_isApp(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v___x_3008_);
lean_dec_ref(v_arg_3007_);
lean_dec_ref(v_arg_3004_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_arg_3010_ = lean_ctor_get(v___x_3008_, 1);
lean_inc_ref(v_arg_3010_);
v___x_3011_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3008_);
v___x_3012_ = l_Lean_Expr_isApp(v___x_3011_);
if (v___x_3012_ == 0)
{
lean_dec_ref(v___x_3011_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_arg_3007_);
lean_dec_ref(v_arg_3004_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_arg_3013_ = lean_ctor_get(v___x_3011_, 1);
lean_inc_ref(v_arg_3013_);
v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
v___x_3015_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3016_ = l_Lean_Expr_isConstOf(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Expr_isApp(v___x_3014_);
if (v___x_3017_ == 0)
{
lean_dec_ref(v___x_3014_);
lean_dec_ref(v_arg_3013_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_arg_3007_);
lean_dec_ref(v_arg_3004_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_arg_3018_ = lean_ctor_get(v___x_3014_, 1);
lean_inc_ref(v_arg_3018_);
v___x_3019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3014_);
v___x_3020_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3021_ = l_Lean_Expr_isConstOf(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_dec_ref(v___x_3019_);
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3013_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_arg_3007_);
lean_dec_ref(v_arg_3004_);
v___y_2991_ = v_a_2955_;
v___y_2992_ = v_a_2956_;
v___y_2993_ = v_a_2957_;
v___y_2994_ = v_a_2958_;
v___y_2995_ = v_a_2959_;
v___y_2996_ = v_a_2960_;
v___y_2997_ = v_a_2961_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3022_; 
lean_dec_ref(v_e_2954_);
v___x_3022_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3019_, v_arg_3018_, v_arg_3013_, v_arg_3010_, v_arg_3007_, v_arg_3004_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
return v___x_3022_;
}
}
}
else
{
lean_object* v___x_3023_; 
lean_dec_ref(v_e_2954_);
v___x_3023_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3014_, v_arg_3013_, v_arg_3010_, v_arg_3007_, v_arg_3004_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
return v___x_3023_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2954_);
return v___x_3000_;
}
v___jp_2963_:
{
if (v___y_2972_ == 0)
{
if (lean_obj_tag(v___y_2970_) == 4)
{
lean_object* v_declName_2973_; lean_object* v___x_2974_; 
v_declName_2973_ = lean_ctor_get(v___y_2970_, 0);
lean_inc(v_declName_2973_);
lean_dec_ref_known(v___y_2970_, 2);
v___x_2974_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2973_, v___y_2967_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; uint8_t v___x_2976_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = lean_unbox(v_a_2975_);
lean_dec(v_a_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2954_, v___y_2966_, v___y_2964_, v___y_2965_, v___y_2971_, v___y_2968_, v___y_2969_, v___y_2967_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2954_, v___y_2966_, v___y_2964_, v___y_2965_, v___y_2971_, v___y_2968_, v___y_2969_, v___y_2967_);
return v___x_2978_;
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v_e_2954_);
v_a_2979_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2974_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2974_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v___x_2987_; 
lean_dec_ref(v___y_2970_);
v___x_2987_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2954_, v___y_2966_, v___y_2964_, v___y_2965_, v___y_2971_, v___y_2968_, v___y_2969_, v___y_2967_);
return v___x_2987_;
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v___y_2970_);
v___x_2988_ = l_Lean_Expr_headBeta(v_e_2954_);
v___x_2989_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2988_, v___y_2966_, v___y_2964_, v___y_2965_, v___y_2971_, v___y_2968_, v___y_2969_, v___y_2967_);
return v___x_2989_;
}
}
v___jp_2990_:
{
lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = l_Lean_Expr_getAppFn(v_e_2954_);
v___x_2999_ = l_Lean_Expr_isLambda(v___x_2998_);
if (v___x_2999_ == 0)
{
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2993_;
v___y_2966_ = v___y_2991_;
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2995_;
v___y_2969_ = v___y_2996_;
v___y_2970_ = v___x_2998_;
v___y_2971_ = v___y_2994_;
v___y_2972_ = v___x_2999_;
goto v___jp_2963_;
}
else
{
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2993_;
v___y_2966_ = v___y_2991_;
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2995_;
v___y_2969_ = v___y_2996_;
v___y_2970_ = v___x_2998_;
v___y_2971_ = v___y_2994_;
v___y_2972_ = v___y_2991_;
goto v___jp_2963_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3027_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3028_ = lean_unsigned_to_nat(18u);
v___x_3029_ = lean_unsigned_to_nat(1913u);
v___x_3030_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3032_ = l_mkPanicMessageWithDecl(v___x_3031_, v___x_3030_, v___x_3029_, v___x_3028_, v___x_3027_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3033_, uint8_t v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = l_Lean_Expr_projExpr_x21(v_e_3033_);
v___x_3043_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3042_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___y_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
if (lean_obj_tag(v_e_3033_) == 11)
{
lean_object* v_typeName_3068_; lean_object* v_idx_3069_; lean_object* v_struct_3070_; size_t v___x_3071_; size_t v___x_3072_; uint8_t v___x_3073_; 
v_typeName_3068_ = lean_ctor_get(v_e_3033_, 0);
v_idx_3069_ = lean_ctor_get(v_e_3033_, 1);
v_struct_3070_ = lean_ctor_get(v_e_3033_, 2);
v___x_3071_ = lean_ptr_addr(v_struct_3070_);
v___x_3072_ = lean_ptr_addr(v_a_3044_);
v___x_3073_ = lean_usize_dec_eq(v___x_3071_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
lean_inc(v_idx_3069_);
lean_inc(v_typeName_3068_);
lean_dec_ref_known(v_e_3033_, 3);
v___x_3074_ = l_Lean_Expr_proj___override(v_typeName_3068_, v_idx_3069_, v_a_3044_);
v___y_3046_ = v___x_3074_;
goto v___jp_3045_;
}
else
{
lean_dec(v_a_3044_);
v___y_3046_ = v_e_3033_;
goto v___jp_3045_;
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_a_3044_);
lean_dec_ref(v_e_3033_);
v___x_3075_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3076_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3075_);
v___y_3046_ = v___x_3076_;
goto v___jp_3045_;
}
v___jp_3045_:
{
lean_object* v___x_3047_; 
lean_inc_ref(v___y_3046_);
v___x_3047_ = l_Lean_Meta_reduceProj_x3f(v___y_3046_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3059_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3059_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3059_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
if (lean_obj_tag(v_a_3048_) == 0)
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___y_3046_);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___y_3046_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
else
{
lean_object* v_val_3055_; lean_object* v___x_3057_; 
lean_dec_ref(v___y_3046_);
v_val_3055_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_val_3055_);
lean_dec_ref_known(v_a_3048_, 1);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_val_3055_);
v___x_3057_ = v___x_3050_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_val_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v___y_3046_);
v_a_3060_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3047_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3047_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3033_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3077_, uint8_t v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
switch(lean_obj_tag(v_e_3077_))
{
case 7:
{
lean_object* v___x_3086_; 
v___x_3086_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3078_ == 0)
{
lean_object* v___x_3087_; lean_object* v_canon_3088_; lean_object* v_cache_3089_; lean_object* v___x_3090_; 
v___x_3087_ = lean_st_ref_get(v_a_3080_);
v_canon_3088_ = lean_ctor_get(v___x_3087_, 9);
lean_inc_ref(v_canon_3088_);
lean_dec(v___x_3087_);
v_cache_3089_ = lean_ctor_get(v_canon_3088_, 0);
lean_inc_ref(v_cache_3089_);
lean_dec_ref(v_canon_3088_);
v___x_3090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3089_, v_e_3077_);
lean_dec_ref(v_cache_3089_);
if (lean_obj_tag(v___x_3090_) == 1)
{
lean_object* v_val_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_val_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set_tag(v___x_3093_, 0);
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_val_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v___x_3099_; 
lean_dec(v___x_3090_);
lean_inc_ref(v_e_3077_);
v___x_3099_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3086_, v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3138_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3138_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3138_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v_canon_3105_; lean_object* v_share_3106_; lean_object* v_maxFVar_3107_; lean_object* v_proofInstInfo_3108_; lean_object* v_inferType_3109_; lean_object* v_getLevel_3110_; lean_object* v_congrInfo_3111_; lean_object* v_defEqI_3112_; lean_object* v_extensions_3113_; lean_object* v_issues_3114_; lean_object* v_instanceOverrides_3115_; uint8_t v_debug_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3137_; 
v___x_3104_ = lean_st_ref_take(v_a_3080_);
v_canon_3105_ = lean_ctor_get(v___x_3104_, 9);
v_share_3106_ = lean_ctor_get(v___x_3104_, 0);
v_maxFVar_3107_ = lean_ctor_get(v___x_3104_, 1);
v_proofInstInfo_3108_ = lean_ctor_get(v___x_3104_, 2);
v_inferType_3109_ = lean_ctor_get(v___x_3104_, 3);
v_getLevel_3110_ = lean_ctor_get(v___x_3104_, 4);
v_congrInfo_3111_ = lean_ctor_get(v___x_3104_, 5);
v_defEqI_3112_ = lean_ctor_get(v___x_3104_, 6);
v_extensions_3113_ = lean_ctor_get(v___x_3104_, 7);
v_issues_3114_ = lean_ctor_get(v___x_3104_, 8);
v_instanceOverrides_3115_ = lean_ctor_get(v___x_3104_, 10);
v_debug_3116_ = lean_ctor_get_uint8(v___x_3104_, sizeof(void*)*11);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3118_ = v___x_3104_;
v_isShared_3119_ = v_isSharedCheck_3137_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_instanceOverrides_3115_);
lean_inc(v_canon_3105_);
lean_inc(v_issues_3114_);
lean_inc(v_extensions_3113_);
lean_inc(v_defEqI_3112_);
lean_inc(v_congrInfo_3111_);
lean_inc(v_getLevel_3110_);
lean_inc(v_inferType_3109_);
lean_inc(v_proofInstInfo_3108_);
lean_inc(v_maxFVar_3107_);
lean_inc(v_share_3106_);
lean_dec(v___x_3104_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3137_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_cache_3120_; lean_object* v_cacheInType_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3136_; 
v_cache_3120_ = lean_ctor_get(v_canon_3105_, 0);
v_cacheInType_3121_ = lean_ctor_get(v_canon_3105_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_canon_3105_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3123_ = v_canon_3105_;
v_isShared_3124_ = v_isSharedCheck_3136_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_cacheInType_3121_);
lean_inc(v_cache_3120_);
lean_dec(v_canon_3105_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3136_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_inc(v_a_3100_);
v___x_3125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3120_, v_e_3077_, v_a_3100_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3125_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_cacheInType_3121_);
v___x_3127_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3129_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 9, v___x_3127_);
v___x_3129_ = v___x_3118_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_share_3106_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_maxFVar_3107_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_proofInstInfo_3108_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_inferType_3109_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_getLevel_3110_);
lean_ctor_set(v_reuseFailAlloc_3134_, 5, v_congrInfo_3111_);
lean_ctor_set(v_reuseFailAlloc_3134_, 6, v_defEqI_3112_);
lean_ctor_set(v_reuseFailAlloc_3134_, 7, v_extensions_3113_);
lean_ctor_set(v_reuseFailAlloc_3134_, 8, v_issues_3114_);
lean_ctor_set(v_reuseFailAlloc_3134_, 9, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3134_, 10, v_instanceOverrides_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3134_, sizeof(void*)*11, v_debug_3116_);
v___x_3129_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_st_ref_put(v_a_3080_, v___x_3129_);
if (v_isShared_3103_ == 0)
{
v___x_3132_ = v___x_3102_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3100_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3099_;
}
}
}
else
{
lean_object* v___x_3139_; lean_object* v_canon_3140_; lean_object* v_cacheInType_3141_; lean_object* v___x_3142_; 
v___x_3139_ = lean_st_ref_get(v_a_3080_);
v_canon_3140_ = lean_ctor_get(v___x_3139_, 9);
lean_inc_ref(v_canon_3140_);
lean_dec(v___x_3139_);
v_cacheInType_3141_ = lean_ctor_get(v_canon_3140_, 1);
lean_inc_ref(v_cacheInType_3141_);
lean_dec_ref(v_canon_3140_);
v___x_3142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3141_, v_e_3077_);
lean_dec_ref(v_cacheInType_3141_);
if (lean_obj_tag(v___x_3142_) == 1)
{
lean_object* v_val_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_val_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 0);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_val_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
lean_object* v___x_3151_; 
lean_dec(v___x_3142_);
lean_inc_ref(v_e_3077_);
v___x_3151_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3086_, v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3190_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3190_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3190_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v_canon_3157_; lean_object* v_share_3158_; lean_object* v_maxFVar_3159_; lean_object* v_proofInstInfo_3160_; lean_object* v_inferType_3161_; lean_object* v_getLevel_3162_; lean_object* v_congrInfo_3163_; lean_object* v_defEqI_3164_; lean_object* v_extensions_3165_; lean_object* v_issues_3166_; lean_object* v_instanceOverrides_3167_; uint8_t v_debug_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3189_; 
v___x_3156_ = lean_st_ref_take(v_a_3080_);
v_canon_3157_ = lean_ctor_get(v___x_3156_, 9);
v_share_3158_ = lean_ctor_get(v___x_3156_, 0);
v_maxFVar_3159_ = lean_ctor_get(v___x_3156_, 1);
v_proofInstInfo_3160_ = lean_ctor_get(v___x_3156_, 2);
v_inferType_3161_ = lean_ctor_get(v___x_3156_, 3);
v_getLevel_3162_ = lean_ctor_get(v___x_3156_, 4);
v_congrInfo_3163_ = lean_ctor_get(v___x_3156_, 5);
v_defEqI_3164_ = lean_ctor_get(v___x_3156_, 6);
v_extensions_3165_ = lean_ctor_get(v___x_3156_, 7);
v_issues_3166_ = lean_ctor_get(v___x_3156_, 8);
v_instanceOverrides_3167_ = lean_ctor_get(v___x_3156_, 10);
v_debug_3168_ = lean_ctor_get_uint8(v___x_3156_, sizeof(void*)*11);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3170_ = v___x_3156_;
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_instanceOverrides_3167_);
lean_inc(v_canon_3157_);
lean_inc(v_issues_3166_);
lean_inc(v_extensions_3165_);
lean_inc(v_defEqI_3164_);
lean_inc(v_congrInfo_3163_);
lean_inc(v_getLevel_3162_);
lean_inc(v_inferType_3161_);
lean_inc(v_proofInstInfo_3160_);
lean_inc(v_maxFVar_3159_);
lean_inc(v_share_3158_);
lean_dec(v___x_3156_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_cache_3172_; lean_object* v_cacheInType_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3188_; 
v_cache_3172_ = lean_ctor_get(v_canon_3157_, 0);
v_cacheInType_3173_ = lean_ctor_get(v_canon_3157_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_canon_3157_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3175_ = v_canon_3157_;
v_isShared_3176_ = v_isSharedCheck_3188_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_cacheInType_3173_);
lean_inc(v_cache_3172_);
lean_dec(v_canon_3157_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3188_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_inc(v_a_3152_);
v___x_3177_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3173_, v_e_3077_, v_a_3152_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_cache_3172_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 9, v___x_3179_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_share_3158_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_maxFVar_3159_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_proofInstInfo_3160_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v_inferType_3161_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v_getLevel_3162_);
lean_ctor_set(v_reuseFailAlloc_3186_, 5, v_congrInfo_3163_);
lean_ctor_set(v_reuseFailAlloc_3186_, 6, v_defEqI_3164_);
lean_ctor_set(v_reuseFailAlloc_3186_, 7, v_extensions_3165_);
lean_ctor_set(v_reuseFailAlloc_3186_, 8, v_issues_3166_);
lean_ctor_set(v_reuseFailAlloc_3186_, 9, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3186_, 10, v_instanceOverrides_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3186_, sizeof(void*)*11, v_debug_3168_);
v___x_3181_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_st_ref_put(v_a_3080_, v___x_3181_);
if (v_isShared_3155_ == 0)
{
v___x_3184_ = v___x_3154_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3152_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3151_;
}
}
}
}
case 6:
{
if (v_a_3078_ == 0)
{
lean_object* v___x_3191_; lean_object* v_canon_3192_; lean_object* v_cache_3193_; lean_object* v___x_3194_; 
v___x_3191_ = lean_st_ref_get(v_a_3080_);
v_canon_3192_ = lean_ctor_get(v___x_3191_, 9);
lean_inc_ref(v_canon_3192_);
lean_dec(v___x_3191_);
v_cache_3193_ = lean_ctor_get(v_canon_3192_, 0);
lean_inc_ref(v_cache_3193_);
lean_dec_ref(v_canon_3192_);
v___x_3194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3193_, v_e_3077_);
lean_dec_ref(v_cache_3193_);
if (lean_obj_tag(v___x_3194_) == 1)
{
lean_object* v_val_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_val_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 0);
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_val_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v___x_3203_; 
lean_dec(v___x_3194_);
lean_inc_ref(v_e_3077_);
v___x_3203_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3242_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3242_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3242_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v_canon_3209_; lean_object* v_share_3210_; lean_object* v_maxFVar_3211_; lean_object* v_proofInstInfo_3212_; lean_object* v_inferType_3213_; lean_object* v_getLevel_3214_; lean_object* v_congrInfo_3215_; lean_object* v_defEqI_3216_; lean_object* v_extensions_3217_; lean_object* v_issues_3218_; lean_object* v_instanceOverrides_3219_; uint8_t v_debug_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3241_; 
v___x_3208_ = lean_st_ref_take(v_a_3080_);
v_canon_3209_ = lean_ctor_get(v___x_3208_, 9);
v_share_3210_ = lean_ctor_get(v___x_3208_, 0);
v_maxFVar_3211_ = lean_ctor_get(v___x_3208_, 1);
v_proofInstInfo_3212_ = lean_ctor_get(v___x_3208_, 2);
v_inferType_3213_ = lean_ctor_get(v___x_3208_, 3);
v_getLevel_3214_ = lean_ctor_get(v___x_3208_, 4);
v_congrInfo_3215_ = lean_ctor_get(v___x_3208_, 5);
v_defEqI_3216_ = lean_ctor_get(v___x_3208_, 6);
v_extensions_3217_ = lean_ctor_get(v___x_3208_, 7);
v_issues_3218_ = lean_ctor_get(v___x_3208_, 8);
v_instanceOverrides_3219_ = lean_ctor_get(v___x_3208_, 10);
v_debug_3220_ = lean_ctor_get_uint8(v___x_3208_, sizeof(void*)*11);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3222_ = v___x_3208_;
v_isShared_3223_ = v_isSharedCheck_3241_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_instanceOverrides_3219_);
lean_inc(v_canon_3209_);
lean_inc(v_issues_3218_);
lean_inc(v_extensions_3217_);
lean_inc(v_defEqI_3216_);
lean_inc(v_congrInfo_3215_);
lean_inc(v_getLevel_3214_);
lean_inc(v_inferType_3213_);
lean_inc(v_proofInstInfo_3212_);
lean_inc(v_maxFVar_3211_);
lean_inc(v_share_3210_);
lean_dec(v___x_3208_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3241_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_cache_3224_; lean_object* v_cacheInType_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3240_; 
v_cache_3224_ = lean_ctor_get(v_canon_3209_, 0);
v_cacheInType_3225_ = lean_ctor_get(v_canon_3209_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_canon_3209_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3227_ = v_canon_3209_;
v_isShared_3228_ = v_isSharedCheck_3240_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_cacheInType_3225_);
lean_inc(v_cache_3224_);
lean_dec(v_canon_3209_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3240_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_inc(v_a_3204_);
v___x_3229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3224_, v_e_3077_, v_a_3204_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_cacheInType_3225_);
v___x_3231_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 9, v___x_3231_);
v___x_3233_ = v___x_3222_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_share_3210_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_maxFVar_3211_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_proofInstInfo_3212_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_inferType_3213_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_getLevel_3214_);
lean_ctor_set(v_reuseFailAlloc_3238_, 5, v_congrInfo_3215_);
lean_ctor_set(v_reuseFailAlloc_3238_, 6, v_defEqI_3216_);
lean_ctor_set(v_reuseFailAlloc_3238_, 7, v_extensions_3217_);
lean_ctor_set(v_reuseFailAlloc_3238_, 8, v_issues_3218_);
lean_ctor_set(v_reuseFailAlloc_3238_, 9, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3238_, 10, v_instanceOverrides_3219_);
lean_ctor_set_uint8(v_reuseFailAlloc_3238_, sizeof(void*)*11, v_debug_3220_);
v___x_3233_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_st_ref_put(v_a_3080_, v___x_3233_);
if (v_isShared_3207_ == 0)
{
v___x_3236_ = v___x_3206_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3204_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3203_;
}
}
}
else
{
lean_object* v___x_3243_; lean_object* v_canon_3244_; lean_object* v_cacheInType_3245_; lean_object* v___x_3246_; 
v___x_3243_ = lean_st_ref_get(v_a_3080_);
v_canon_3244_ = lean_ctor_get(v___x_3243_, 9);
lean_inc_ref(v_canon_3244_);
lean_dec(v___x_3243_);
v_cacheInType_3245_ = lean_ctor_get(v_canon_3244_, 1);
lean_inc_ref(v_cacheInType_3245_);
lean_dec_ref(v_canon_3244_);
v___x_3246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3245_, v_e_3077_);
lean_dec_ref(v_cacheInType_3245_);
if (lean_obj_tag(v___x_3246_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_val_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 0);
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
else
{
lean_object* v___x_3255_; 
lean_dec(v___x_3246_);
lean_inc_ref(v_e_3077_);
v___x_3255_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3294_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3294_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3294_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; lean_object* v_canon_3261_; lean_object* v_share_3262_; lean_object* v_maxFVar_3263_; lean_object* v_proofInstInfo_3264_; lean_object* v_inferType_3265_; lean_object* v_getLevel_3266_; lean_object* v_congrInfo_3267_; lean_object* v_defEqI_3268_; lean_object* v_extensions_3269_; lean_object* v_issues_3270_; lean_object* v_instanceOverrides_3271_; uint8_t v_debug_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3293_; 
v___x_3260_ = lean_st_ref_take(v_a_3080_);
v_canon_3261_ = lean_ctor_get(v___x_3260_, 9);
v_share_3262_ = lean_ctor_get(v___x_3260_, 0);
v_maxFVar_3263_ = lean_ctor_get(v___x_3260_, 1);
v_proofInstInfo_3264_ = lean_ctor_get(v___x_3260_, 2);
v_inferType_3265_ = lean_ctor_get(v___x_3260_, 3);
v_getLevel_3266_ = lean_ctor_get(v___x_3260_, 4);
v_congrInfo_3267_ = lean_ctor_get(v___x_3260_, 5);
v_defEqI_3268_ = lean_ctor_get(v___x_3260_, 6);
v_extensions_3269_ = lean_ctor_get(v___x_3260_, 7);
v_issues_3270_ = lean_ctor_get(v___x_3260_, 8);
v_instanceOverrides_3271_ = lean_ctor_get(v___x_3260_, 10);
v_debug_3272_ = lean_ctor_get_uint8(v___x_3260_, sizeof(void*)*11);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3274_ = v___x_3260_;
v_isShared_3275_ = v_isSharedCheck_3293_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_instanceOverrides_3271_);
lean_inc(v_canon_3261_);
lean_inc(v_issues_3270_);
lean_inc(v_extensions_3269_);
lean_inc(v_defEqI_3268_);
lean_inc(v_congrInfo_3267_);
lean_inc(v_getLevel_3266_);
lean_inc(v_inferType_3265_);
lean_inc(v_proofInstInfo_3264_);
lean_inc(v_maxFVar_3263_);
lean_inc(v_share_3262_);
lean_dec(v___x_3260_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3293_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_cache_3276_; lean_object* v_cacheInType_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3292_; 
v_cache_3276_ = lean_ctor_get(v_canon_3261_, 0);
v_cacheInType_3277_ = lean_ctor_get(v_canon_3261_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_canon_3261_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3279_ = v_canon_3261_;
v_isShared_3280_ = v_isSharedCheck_3292_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_cacheInType_3277_);
lean_inc(v_cache_3276_);
lean_dec(v_canon_3261_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3292_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_inc(v_a_3256_);
v___x_3281_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3277_, v_e_3077_, v_a_3256_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 1, v___x_3281_);
v___x_3283_ = v___x_3279_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_cache_3276_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3285_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 9, v___x_3283_);
v___x_3285_ = v___x_3274_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_share_3262_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_maxFVar_3263_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_proofInstInfo_3264_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_inferType_3265_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v_getLevel_3266_);
lean_ctor_set(v_reuseFailAlloc_3290_, 5, v_congrInfo_3267_);
lean_ctor_set(v_reuseFailAlloc_3290_, 6, v_defEqI_3268_);
lean_ctor_set(v_reuseFailAlloc_3290_, 7, v_extensions_3269_);
lean_ctor_set(v_reuseFailAlloc_3290_, 8, v_issues_3270_);
lean_ctor_set(v_reuseFailAlloc_3290_, 9, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3290_, 10, v_instanceOverrides_3271_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*11, v_debug_3272_);
v___x_3285_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3286_ = lean_st_ref_put(v_a_3080_, v___x_3285_);
if (v_isShared_3259_ == 0)
{
v___x_3288_ = v___x_3258_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3256_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3255_;
}
}
}
}
case 8:
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3078_ == 0)
{
lean_object* v___x_3296_; lean_object* v_canon_3297_; lean_object* v_cache_3298_; lean_object* v___x_3299_; 
v___x_3296_ = lean_st_ref_get(v_a_3080_);
v_canon_3297_ = lean_ctor_get(v___x_3296_, 9);
lean_inc_ref(v_canon_3297_);
lean_dec(v___x_3296_);
v_cache_3298_ = lean_ctor_get(v_canon_3297_, 0);
lean_inc_ref(v_cache_3298_);
lean_dec_ref(v_canon_3297_);
v___x_3299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3298_, v_e_3077_);
lean_dec_ref(v_cache_3298_);
if (lean_obj_tag(v___x_3299_) == 1)
{
lean_object* v_val_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref_known(v_e_3077_, 4);
v_val_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_val_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 0);
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
else
{
lean_object* v___x_3308_; 
lean_dec(v___x_3299_);
lean_inc_ref(v_e_3077_);
v___x_3308_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3295_, v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3347_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3347_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3347_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v_canon_3314_; lean_object* v_share_3315_; lean_object* v_maxFVar_3316_; lean_object* v_proofInstInfo_3317_; lean_object* v_inferType_3318_; lean_object* v_getLevel_3319_; lean_object* v_congrInfo_3320_; lean_object* v_defEqI_3321_; lean_object* v_extensions_3322_; lean_object* v_issues_3323_; lean_object* v_instanceOverrides_3324_; uint8_t v_debug_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3346_; 
v___x_3313_ = lean_st_ref_take(v_a_3080_);
v_canon_3314_ = lean_ctor_get(v___x_3313_, 9);
v_share_3315_ = lean_ctor_get(v___x_3313_, 0);
v_maxFVar_3316_ = lean_ctor_get(v___x_3313_, 1);
v_proofInstInfo_3317_ = lean_ctor_get(v___x_3313_, 2);
v_inferType_3318_ = lean_ctor_get(v___x_3313_, 3);
v_getLevel_3319_ = lean_ctor_get(v___x_3313_, 4);
v_congrInfo_3320_ = lean_ctor_get(v___x_3313_, 5);
v_defEqI_3321_ = lean_ctor_get(v___x_3313_, 6);
v_extensions_3322_ = lean_ctor_get(v___x_3313_, 7);
v_issues_3323_ = lean_ctor_get(v___x_3313_, 8);
v_instanceOverrides_3324_ = lean_ctor_get(v___x_3313_, 10);
v_debug_3325_ = lean_ctor_get_uint8(v___x_3313_, sizeof(void*)*11);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3327_ = v___x_3313_;
v_isShared_3328_ = v_isSharedCheck_3346_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_instanceOverrides_3324_);
lean_inc(v_canon_3314_);
lean_inc(v_issues_3323_);
lean_inc(v_extensions_3322_);
lean_inc(v_defEqI_3321_);
lean_inc(v_congrInfo_3320_);
lean_inc(v_getLevel_3319_);
lean_inc(v_inferType_3318_);
lean_inc(v_proofInstInfo_3317_);
lean_inc(v_maxFVar_3316_);
lean_inc(v_share_3315_);
lean_dec(v___x_3313_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3346_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_cache_3329_; lean_object* v_cacheInType_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3345_; 
v_cache_3329_ = lean_ctor_get(v_canon_3314_, 0);
v_cacheInType_3330_ = lean_ctor_get(v_canon_3314_, 1);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_canon_3314_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3332_ = v_canon_3314_;
v_isShared_3333_ = v_isSharedCheck_3345_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_cacheInType_3330_);
lean_inc(v_cache_3329_);
lean_dec(v_canon_3314_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3345_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_inc(v_a_3309_);
v___x_3334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3329_, v_e_3077_, v_a_3309_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3334_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_cacheInType_3330_);
v___x_3336_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 9, v___x_3336_);
v___x_3338_ = v___x_3327_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_share_3315_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_maxFVar_3316_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_proofInstInfo_3317_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_inferType_3318_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_getLevel_3319_);
lean_ctor_set(v_reuseFailAlloc_3343_, 5, v_congrInfo_3320_);
lean_ctor_set(v_reuseFailAlloc_3343_, 6, v_defEqI_3321_);
lean_ctor_set(v_reuseFailAlloc_3343_, 7, v_extensions_3322_);
lean_ctor_set(v_reuseFailAlloc_3343_, 8, v_issues_3323_);
lean_ctor_set(v_reuseFailAlloc_3343_, 9, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3343_, 10, v_instanceOverrides_3324_);
lean_ctor_set_uint8(v_reuseFailAlloc_3343_, sizeof(void*)*11, v_debug_3325_);
v___x_3338_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = lean_st_ref_put(v_a_3080_, v___x_3338_);
if (v_isShared_3312_ == 0)
{
v___x_3341_ = v___x_3311_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3309_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 4);
return v___x_3308_;
}
}
}
else
{
lean_object* v___x_3348_; lean_object* v_canon_3349_; lean_object* v_cacheInType_3350_; lean_object* v___x_3351_; 
v___x_3348_ = lean_st_ref_get(v_a_3080_);
v_canon_3349_ = lean_ctor_get(v___x_3348_, 9);
lean_inc_ref(v_canon_3349_);
lean_dec(v___x_3348_);
v_cacheInType_3350_ = lean_ctor_get(v_canon_3349_, 1);
lean_inc_ref(v_cacheInType_3350_);
lean_dec_ref(v_canon_3349_);
v___x_3351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3350_, v_e_3077_);
lean_dec_ref(v_cacheInType_3350_);
if (lean_obj_tag(v___x_3351_) == 1)
{
lean_object* v_val_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref_known(v_e_3077_, 4);
v_val_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_val_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set_tag(v___x_3354_, 0);
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_val_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_object* v___x_3360_; 
lean_dec(v___x_3351_);
lean_inc_ref(v_e_3077_);
v___x_3360_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3295_, v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3399_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3399_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3399_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v_canon_3366_; lean_object* v_share_3367_; lean_object* v_maxFVar_3368_; lean_object* v_proofInstInfo_3369_; lean_object* v_inferType_3370_; lean_object* v_getLevel_3371_; lean_object* v_congrInfo_3372_; lean_object* v_defEqI_3373_; lean_object* v_extensions_3374_; lean_object* v_issues_3375_; lean_object* v_instanceOverrides_3376_; uint8_t v_debug_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3398_; 
v___x_3365_ = lean_st_ref_take(v_a_3080_);
v_canon_3366_ = lean_ctor_get(v___x_3365_, 9);
v_share_3367_ = lean_ctor_get(v___x_3365_, 0);
v_maxFVar_3368_ = lean_ctor_get(v___x_3365_, 1);
v_proofInstInfo_3369_ = lean_ctor_get(v___x_3365_, 2);
v_inferType_3370_ = lean_ctor_get(v___x_3365_, 3);
v_getLevel_3371_ = lean_ctor_get(v___x_3365_, 4);
v_congrInfo_3372_ = lean_ctor_get(v___x_3365_, 5);
v_defEqI_3373_ = lean_ctor_get(v___x_3365_, 6);
v_extensions_3374_ = lean_ctor_get(v___x_3365_, 7);
v_issues_3375_ = lean_ctor_get(v___x_3365_, 8);
v_instanceOverrides_3376_ = lean_ctor_get(v___x_3365_, 10);
v_debug_3377_ = lean_ctor_get_uint8(v___x_3365_, sizeof(void*)*11);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3379_ = v___x_3365_;
v_isShared_3380_ = v_isSharedCheck_3398_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_instanceOverrides_3376_);
lean_inc(v_canon_3366_);
lean_inc(v_issues_3375_);
lean_inc(v_extensions_3374_);
lean_inc(v_defEqI_3373_);
lean_inc(v_congrInfo_3372_);
lean_inc(v_getLevel_3371_);
lean_inc(v_inferType_3370_);
lean_inc(v_proofInstInfo_3369_);
lean_inc(v_maxFVar_3368_);
lean_inc(v_share_3367_);
lean_dec(v___x_3365_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3398_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_cache_3381_; lean_object* v_cacheInType_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3397_; 
v_cache_3381_ = lean_ctor_get(v_canon_3366_, 0);
v_cacheInType_3382_ = lean_ctor_get(v_canon_3366_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_canon_3366_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3384_ = v_canon_3366_;
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_cacheInType_3382_);
lean_inc(v_cache_3381_);
lean_dec(v_canon_3366_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
lean_inc(v_a_3361_);
v___x_3386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3382_, v_e_3077_, v_a_3361_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v___x_3386_);
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_cache_3381_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 9, v___x_3388_);
v___x_3390_ = v___x_3379_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_share_3367_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_maxFVar_3368_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_proofInstInfo_3369_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_inferType_3370_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v_getLevel_3371_);
lean_ctor_set(v_reuseFailAlloc_3395_, 5, v_congrInfo_3372_);
lean_ctor_set(v_reuseFailAlloc_3395_, 6, v_defEqI_3373_);
lean_ctor_set(v_reuseFailAlloc_3395_, 7, v_extensions_3374_);
lean_ctor_set(v_reuseFailAlloc_3395_, 8, v_issues_3375_);
lean_ctor_set(v_reuseFailAlloc_3395_, 9, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3395_, 10, v_instanceOverrides_3376_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, sizeof(void*)*11, v_debug_3377_);
v___x_3390_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3391_ = lean_st_ref_put(v_a_3080_, v___x_3390_);
if (v_isShared_3364_ == 0)
{
v___x_3393_ = v___x_3363_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3361_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 4);
return v___x_3360_;
}
}
}
}
case 5:
{
if (v_a_3078_ == 0)
{
lean_object* v___x_3400_; lean_object* v_canon_3401_; lean_object* v_cache_3402_; lean_object* v___x_3403_; 
v___x_3400_ = lean_st_ref_get(v_a_3080_);
v_canon_3401_ = lean_ctor_get(v___x_3400_, 9);
lean_inc_ref(v_canon_3401_);
lean_dec(v___x_3400_);
v_cache_3402_ = lean_ctor_get(v_canon_3401_, 0);
lean_inc_ref(v_cache_3402_);
lean_dec_ref(v_canon_3401_);
v___x_3403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3402_, v_e_3077_);
lean_dec_ref(v_cache_3402_);
if (lean_obj_tag(v___x_3403_) == 1)
{
lean_object* v_val_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref_known(v_e_3077_, 2);
v_val_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_val_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 0);
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_val_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
else
{
lean_object* v___x_3412_; 
lean_dec(v___x_3403_);
lean_inc_ref(v_e_3077_);
v___x_3412_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3451_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3451_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3451_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v_canon_3418_; lean_object* v_share_3419_; lean_object* v_maxFVar_3420_; lean_object* v_proofInstInfo_3421_; lean_object* v_inferType_3422_; lean_object* v_getLevel_3423_; lean_object* v_congrInfo_3424_; lean_object* v_defEqI_3425_; lean_object* v_extensions_3426_; lean_object* v_issues_3427_; lean_object* v_instanceOverrides_3428_; uint8_t v_debug_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3450_; 
v___x_3417_ = lean_st_ref_take(v_a_3080_);
v_canon_3418_ = lean_ctor_get(v___x_3417_, 9);
v_share_3419_ = lean_ctor_get(v___x_3417_, 0);
v_maxFVar_3420_ = lean_ctor_get(v___x_3417_, 1);
v_proofInstInfo_3421_ = lean_ctor_get(v___x_3417_, 2);
v_inferType_3422_ = lean_ctor_get(v___x_3417_, 3);
v_getLevel_3423_ = lean_ctor_get(v___x_3417_, 4);
v_congrInfo_3424_ = lean_ctor_get(v___x_3417_, 5);
v_defEqI_3425_ = lean_ctor_get(v___x_3417_, 6);
v_extensions_3426_ = lean_ctor_get(v___x_3417_, 7);
v_issues_3427_ = lean_ctor_get(v___x_3417_, 8);
v_instanceOverrides_3428_ = lean_ctor_get(v___x_3417_, 10);
v_debug_3429_ = lean_ctor_get_uint8(v___x_3417_, sizeof(void*)*11);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3431_ = v___x_3417_;
v_isShared_3432_ = v_isSharedCheck_3450_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_instanceOverrides_3428_);
lean_inc(v_canon_3418_);
lean_inc(v_issues_3427_);
lean_inc(v_extensions_3426_);
lean_inc(v_defEqI_3425_);
lean_inc(v_congrInfo_3424_);
lean_inc(v_getLevel_3423_);
lean_inc(v_inferType_3422_);
lean_inc(v_proofInstInfo_3421_);
lean_inc(v_maxFVar_3420_);
lean_inc(v_share_3419_);
lean_dec(v___x_3417_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3450_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_cache_3433_; lean_object* v_cacheInType_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3449_; 
v_cache_3433_ = lean_ctor_get(v_canon_3418_, 0);
v_cacheInType_3434_ = lean_ctor_get(v_canon_3418_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_canon_3418_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3436_ = v_canon_3418_;
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_cacheInType_3434_);
lean_inc(v_cache_3433_);
lean_dec(v_canon_3418_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
lean_inc(v_a_3413_);
v___x_3438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3433_, v_e_3077_, v_a_3413_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_cacheInType_3434_);
v___x_3440_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 9, v___x_3440_);
v___x_3442_ = v___x_3431_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_share_3419_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_maxFVar_3420_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_proofInstInfo_3421_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_inferType_3422_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_getLevel_3423_);
lean_ctor_set(v_reuseFailAlloc_3447_, 5, v_congrInfo_3424_);
lean_ctor_set(v_reuseFailAlloc_3447_, 6, v_defEqI_3425_);
lean_ctor_set(v_reuseFailAlloc_3447_, 7, v_extensions_3426_);
lean_ctor_set(v_reuseFailAlloc_3447_, 8, v_issues_3427_);
lean_ctor_set(v_reuseFailAlloc_3447_, 9, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3447_, 10, v_instanceOverrides_3428_);
lean_ctor_set_uint8(v_reuseFailAlloc_3447_, sizeof(void*)*11, v_debug_3429_);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_st_ref_put(v_a_3080_, v___x_3442_);
if (v_isShared_3416_ == 0)
{
v___x_3445_ = v___x_3415_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3413_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 2);
return v___x_3412_;
}
}
}
else
{
lean_object* v___x_3452_; lean_object* v_canon_3453_; lean_object* v_cacheInType_3454_; lean_object* v___x_3455_; 
v___x_3452_ = lean_st_ref_get(v_a_3080_);
v_canon_3453_ = lean_ctor_get(v___x_3452_, 9);
lean_inc_ref(v_canon_3453_);
lean_dec(v___x_3452_);
v_cacheInType_3454_ = lean_ctor_get(v_canon_3453_, 1);
lean_inc_ref(v_cacheInType_3454_);
lean_dec_ref(v_canon_3453_);
v___x_3455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3454_, v_e_3077_);
lean_dec_ref(v_cacheInType_3454_);
if (lean_obj_tag(v___x_3455_) == 1)
{
lean_object* v_val_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref_known(v_e_3077_, 2);
v_val_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_val_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 0);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_val_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
else
{
lean_object* v___x_3464_; 
lean_dec(v___x_3455_);
lean_inc_ref(v_e_3077_);
v___x_3464_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3503_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3503_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3503_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v_canon_3470_; lean_object* v_share_3471_; lean_object* v_maxFVar_3472_; lean_object* v_proofInstInfo_3473_; lean_object* v_inferType_3474_; lean_object* v_getLevel_3475_; lean_object* v_congrInfo_3476_; lean_object* v_defEqI_3477_; lean_object* v_extensions_3478_; lean_object* v_issues_3479_; lean_object* v_instanceOverrides_3480_; uint8_t v_debug_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3502_; 
v___x_3469_ = lean_st_ref_take(v_a_3080_);
v_canon_3470_ = lean_ctor_get(v___x_3469_, 9);
v_share_3471_ = lean_ctor_get(v___x_3469_, 0);
v_maxFVar_3472_ = lean_ctor_get(v___x_3469_, 1);
v_proofInstInfo_3473_ = lean_ctor_get(v___x_3469_, 2);
v_inferType_3474_ = lean_ctor_get(v___x_3469_, 3);
v_getLevel_3475_ = lean_ctor_get(v___x_3469_, 4);
v_congrInfo_3476_ = lean_ctor_get(v___x_3469_, 5);
v_defEqI_3477_ = lean_ctor_get(v___x_3469_, 6);
v_extensions_3478_ = lean_ctor_get(v___x_3469_, 7);
v_issues_3479_ = lean_ctor_get(v___x_3469_, 8);
v_instanceOverrides_3480_ = lean_ctor_get(v___x_3469_, 10);
v_debug_3481_ = lean_ctor_get_uint8(v___x_3469_, sizeof(void*)*11);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3483_ = v___x_3469_;
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_instanceOverrides_3480_);
lean_inc(v_canon_3470_);
lean_inc(v_issues_3479_);
lean_inc(v_extensions_3478_);
lean_inc(v_defEqI_3477_);
lean_inc(v_congrInfo_3476_);
lean_inc(v_getLevel_3475_);
lean_inc(v_inferType_3474_);
lean_inc(v_proofInstInfo_3473_);
lean_inc(v_maxFVar_3472_);
lean_inc(v_share_3471_);
lean_dec(v___x_3469_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_cache_3485_; lean_object* v_cacheInType_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3501_; 
v_cache_3485_ = lean_ctor_get(v_canon_3470_, 0);
v_cacheInType_3486_ = lean_ctor_get(v_canon_3470_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_canon_3470_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3488_ = v_canon_3470_;
v_isShared_3489_ = v_isSharedCheck_3501_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_cacheInType_3486_);
lean_inc(v_cache_3485_);
lean_dec(v_canon_3470_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3501_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_inc(v_a_3465_);
v___x_3490_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3486_, v_e_3077_, v_a_3465_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v___x_3490_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_cache_3485_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 9, v___x_3492_);
v___x_3494_ = v___x_3483_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_share_3471_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_maxFVar_3472_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_proofInstInfo_3473_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_inferType_3474_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_getLevel_3475_);
lean_ctor_set(v_reuseFailAlloc_3499_, 5, v_congrInfo_3476_);
lean_ctor_set(v_reuseFailAlloc_3499_, 6, v_defEqI_3477_);
lean_ctor_set(v_reuseFailAlloc_3499_, 7, v_extensions_3478_);
lean_ctor_set(v_reuseFailAlloc_3499_, 8, v_issues_3479_);
lean_ctor_set(v_reuseFailAlloc_3499_, 9, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3499_, 10, v_instanceOverrides_3480_);
lean_ctor_set_uint8(v_reuseFailAlloc_3499_, sizeof(void*)*11, v_debug_3481_);
v___x_3494_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_st_ref_put(v_a_3080_, v___x_3494_);
if (v_isShared_3468_ == 0)
{
v___x_3497_ = v___x_3467_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3465_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 2);
return v___x_3464_;
}
}
}
}
case 11:
{
if (v_a_3078_ == 0)
{
lean_object* v___x_3504_; lean_object* v_canon_3505_; lean_object* v_cache_3506_; lean_object* v___x_3507_; 
v___x_3504_ = lean_st_ref_get(v_a_3080_);
v_canon_3505_ = lean_ctor_get(v___x_3504_, 9);
lean_inc_ref(v_canon_3505_);
lean_dec(v___x_3504_);
v_cache_3506_ = lean_ctor_get(v_canon_3505_, 0);
lean_inc_ref(v_cache_3506_);
lean_dec_ref(v_canon_3505_);
v___x_3507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3506_, v_e_3077_);
lean_dec_ref(v_cache_3506_);
if (lean_obj_tag(v___x_3507_) == 1)
{
lean_object* v_val_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_val_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 0);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_val_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v___x_3507_);
lean_inc_ref(v_e_3077_);
v___x_3516_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3555_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3555_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3555_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v_canon_3522_; lean_object* v_share_3523_; lean_object* v_maxFVar_3524_; lean_object* v_proofInstInfo_3525_; lean_object* v_inferType_3526_; lean_object* v_getLevel_3527_; lean_object* v_congrInfo_3528_; lean_object* v_defEqI_3529_; lean_object* v_extensions_3530_; lean_object* v_issues_3531_; lean_object* v_instanceOverrides_3532_; uint8_t v_debug_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3554_; 
v___x_3521_ = lean_st_ref_take(v_a_3080_);
v_canon_3522_ = lean_ctor_get(v___x_3521_, 9);
v_share_3523_ = lean_ctor_get(v___x_3521_, 0);
v_maxFVar_3524_ = lean_ctor_get(v___x_3521_, 1);
v_proofInstInfo_3525_ = lean_ctor_get(v___x_3521_, 2);
v_inferType_3526_ = lean_ctor_get(v___x_3521_, 3);
v_getLevel_3527_ = lean_ctor_get(v___x_3521_, 4);
v_congrInfo_3528_ = lean_ctor_get(v___x_3521_, 5);
v_defEqI_3529_ = lean_ctor_get(v___x_3521_, 6);
v_extensions_3530_ = lean_ctor_get(v___x_3521_, 7);
v_issues_3531_ = lean_ctor_get(v___x_3521_, 8);
v_instanceOverrides_3532_ = lean_ctor_get(v___x_3521_, 10);
v_debug_3533_ = lean_ctor_get_uint8(v___x_3521_, sizeof(void*)*11);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3535_ = v___x_3521_;
v_isShared_3536_ = v_isSharedCheck_3554_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_instanceOverrides_3532_);
lean_inc(v_canon_3522_);
lean_inc(v_issues_3531_);
lean_inc(v_extensions_3530_);
lean_inc(v_defEqI_3529_);
lean_inc(v_congrInfo_3528_);
lean_inc(v_getLevel_3527_);
lean_inc(v_inferType_3526_);
lean_inc(v_proofInstInfo_3525_);
lean_inc(v_maxFVar_3524_);
lean_inc(v_share_3523_);
lean_dec(v___x_3521_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3554_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_cache_3537_; lean_object* v_cacheInType_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3553_; 
v_cache_3537_ = lean_ctor_get(v_canon_3522_, 0);
v_cacheInType_3538_ = lean_ctor_get(v_canon_3522_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_canon_3522_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3540_ = v_canon_3522_;
v_isShared_3541_ = v_isSharedCheck_3553_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_cacheInType_3538_);
lean_inc(v_cache_3537_);
lean_dec(v_canon_3522_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3553_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_inc(v_a_3517_);
v___x_3542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3537_, v_e_3077_, v_a_3517_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v___x_3542_);
v___x_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_cacheInType_3538_);
v___x_3544_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3546_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 9, v___x_3544_);
v___x_3546_ = v___x_3535_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_share_3523_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_maxFVar_3524_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_proofInstInfo_3525_);
lean_ctor_set(v_reuseFailAlloc_3551_, 3, v_inferType_3526_);
lean_ctor_set(v_reuseFailAlloc_3551_, 4, v_getLevel_3527_);
lean_ctor_set(v_reuseFailAlloc_3551_, 5, v_congrInfo_3528_);
lean_ctor_set(v_reuseFailAlloc_3551_, 6, v_defEqI_3529_);
lean_ctor_set(v_reuseFailAlloc_3551_, 7, v_extensions_3530_);
lean_ctor_set(v_reuseFailAlloc_3551_, 8, v_issues_3531_);
lean_ctor_set(v_reuseFailAlloc_3551_, 9, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3551_, 10, v_instanceOverrides_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3551_, sizeof(void*)*11, v_debug_3533_);
v___x_3546_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = lean_st_ref_put(v_a_3080_, v___x_3546_);
if (v_isShared_3520_ == 0)
{
v___x_3549_ = v___x_3519_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3517_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3516_;
}
}
}
else
{
lean_object* v___x_3556_; lean_object* v_canon_3557_; lean_object* v_cacheInType_3558_; lean_object* v___x_3559_; 
v___x_3556_ = lean_st_ref_get(v_a_3080_);
v_canon_3557_ = lean_ctor_get(v___x_3556_, 9);
lean_inc_ref(v_canon_3557_);
lean_dec(v___x_3556_);
v_cacheInType_3558_ = lean_ctor_get(v_canon_3557_, 1);
lean_inc_ref(v_cacheInType_3558_);
lean_dec_ref(v_canon_3557_);
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3558_, v_e_3077_);
lean_dec_ref(v_cacheInType_3558_);
if (lean_obj_tag(v___x_3559_) == 1)
{
lean_object* v_val_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec_ref_known(v_e_3077_, 3);
v_val_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_val_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set_tag(v___x_3562_, 0);
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_val_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
else
{
lean_object* v___x_3568_; 
lean_dec(v___x_3559_);
lean_inc_ref(v_e_3077_);
v___x_3568_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3607_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3607_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3607_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v_canon_3574_; lean_object* v_share_3575_; lean_object* v_maxFVar_3576_; lean_object* v_proofInstInfo_3577_; lean_object* v_inferType_3578_; lean_object* v_getLevel_3579_; lean_object* v_congrInfo_3580_; lean_object* v_defEqI_3581_; lean_object* v_extensions_3582_; lean_object* v_issues_3583_; lean_object* v_instanceOverrides_3584_; uint8_t v_debug_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3606_; 
v___x_3573_ = lean_st_ref_take(v_a_3080_);
v_canon_3574_ = lean_ctor_get(v___x_3573_, 9);
v_share_3575_ = lean_ctor_get(v___x_3573_, 0);
v_maxFVar_3576_ = lean_ctor_get(v___x_3573_, 1);
v_proofInstInfo_3577_ = lean_ctor_get(v___x_3573_, 2);
v_inferType_3578_ = lean_ctor_get(v___x_3573_, 3);
v_getLevel_3579_ = lean_ctor_get(v___x_3573_, 4);
v_congrInfo_3580_ = lean_ctor_get(v___x_3573_, 5);
v_defEqI_3581_ = lean_ctor_get(v___x_3573_, 6);
v_extensions_3582_ = lean_ctor_get(v___x_3573_, 7);
v_issues_3583_ = lean_ctor_get(v___x_3573_, 8);
v_instanceOverrides_3584_ = lean_ctor_get(v___x_3573_, 10);
v_debug_3585_ = lean_ctor_get_uint8(v___x_3573_, sizeof(void*)*11);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3587_ = v___x_3573_;
v_isShared_3588_ = v_isSharedCheck_3606_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_instanceOverrides_3584_);
lean_inc(v_canon_3574_);
lean_inc(v_issues_3583_);
lean_inc(v_extensions_3582_);
lean_inc(v_defEqI_3581_);
lean_inc(v_congrInfo_3580_);
lean_inc(v_getLevel_3579_);
lean_inc(v_inferType_3578_);
lean_inc(v_proofInstInfo_3577_);
lean_inc(v_maxFVar_3576_);
lean_inc(v_share_3575_);
lean_dec(v___x_3573_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3606_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_cache_3589_; lean_object* v_cacheInType_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3605_; 
v_cache_3589_ = lean_ctor_get(v_canon_3574_, 0);
v_cacheInType_3590_ = lean_ctor_get(v_canon_3574_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_canon_3574_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3592_ = v_canon_3574_;
v_isShared_3593_ = v_isSharedCheck_3605_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_cacheInType_3590_);
lean_inc(v_cache_3589_);
lean_dec(v_canon_3574_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3605_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
lean_inc(v_a_3569_);
v___x_3594_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3590_, v_e_3077_, v_a_3569_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 1, v___x_3594_);
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_cache_3589_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 9, v___x_3596_);
v___x_3598_ = v___x_3587_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_share_3575_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_maxFVar_3576_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_proofInstInfo_3577_);
lean_ctor_set(v_reuseFailAlloc_3603_, 3, v_inferType_3578_);
lean_ctor_set(v_reuseFailAlloc_3603_, 4, v_getLevel_3579_);
lean_ctor_set(v_reuseFailAlloc_3603_, 5, v_congrInfo_3580_);
lean_ctor_set(v_reuseFailAlloc_3603_, 6, v_defEqI_3581_);
lean_ctor_set(v_reuseFailAlloc_3603_, 7, v_extensions_3582_);
lean_ctor_set(v_reuseFailAlloc_3603_, 8, v_issues_3583_);
lean_ctor_set(v_reuseFailAlloc_3603_, 9, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3603_, 10, v_instanceOverrides_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*11, v_debug_3585_);
v___x_3598_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_st_ref_put(v_a_3080_, v___x_3598_);
if (v_isShared_3572_ == 0)
{
v___x_3601_ = v___x_3571_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3569_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 3);
return v___x_3568_;
}
}
}
}
case 10:
{
lean_object* v_data_3608_; lean_object* v_expr_3609_; lean_object* v___x_3610_; 
v_data_3608_ = lean_ctor_get(v_e_3077_, 0);
v_expr_3609_ = lean_ctor_get(v_e_3077_, 1);
lean_inc_ref(v_expr_3609_);
v___x_3610_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3609_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3625_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3625_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3625_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
size_t v___x_3615_; size_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3615_ = lean_ptr_addr(v_expr_3609_);
v___x_3616_ = lean_ptr_addr(v_a_3611_);
v___x_3617_ = lean_usize_dec_eq(v___x_3615_, v___x_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_inc(v_data_3608_);
lean_dec_ref_known(v_e_3077_, 2);
v___x_3618_ = l_Lean_Expr_mdata___override(v_data_3608_, v_a_3611_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3618_);
v___x_3620_ = v___x_3613_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
else
{
lean_object* v___x_3623_; 
lean_dec(v_a_3611_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v_e_3077_);
v___x_3623_ = v___x_3613_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_e_3077_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3077_, 2);
return v___x_3610_;
}
}
default: 
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_e_3077_);
return v___x_3626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3627_, uint8_t v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
if (v_a_3628_ == 0)
{
uint8_t v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = 1;
lean_inc_ref(v_e_3627_);
v___x_3637_ = l_Lean_Meta_isProp(v_e_3627_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; uint8_t v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___x_3639_ = lean_unbox(v_a_3638_);
lean_dec(v_a_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3627_, v___x_3636_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3640_;
}
else
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3641_;
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_e_3627_);
v_a_3642_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3637_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3637_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3651_, lean_object* v_e_3652_, uint8_t v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
if (lean_obj_tag(v_e_3652_) == 7)
{
lean_object* v_binderName_3661_; lean_object* v_binderType_3662_; lean_object* v_body_3663_; uint8_t v_binderInfo_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_binderName_3661_ = lean_ctor_get(v_e_3652_, 0);
lean_inc(v_binderName_3661_);
v_binderType_3662_ = lean_ctor_get(v_e_3652_, 1);
lean_inc_ref(v_binderType_3662_);
v_body_3663_ = lean_ctor_get(v_e_3652_, 2);
lean_inc_ref(v_body_3663_);
v_binderInfo_3664_ = lean_ctor_get_uint8(v_e_3652_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3652_, 3);
lean_inc_ref(v_fvars_3651_);
v___f_3665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3665_, 0, v_fvars_3651_);
lean_closure_set(v___f_3665_, 1, v_body_3663_);
v___x_3666_ = lean_expr_instantiate_rev(v_binderType_3662_, v_fvars_3651_);
lean_dec_ref(v_fvars_3651_);
lean_dec_ref(v_binderType_3662_);
v___x_3667_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3666_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = 0;
v___x_3670_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_3661_, v_binderInfo_3664_, v_a_3668_, v___f_3665_, v___x_3669_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
return v___x_3670_;
}
else
{
lean_dec_ref(v___f_3665_);
lean_dec(v_binderName_3661_);
return v___x_3667_;
}
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_expr_instantiate_rev(v_e_3652_, v_fvars_3651_);
lean_dec_ref(v_e_3652_);
v___x_3672_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3671_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; uint8_t v___x_3674_; uint8_t v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = 0;
v___x_3675_ = 1;
v___x_3676_ = 1;
v___x_3677_ = l_Lean_Meta_mkForallFVars(v_fvars_3651_, v_a_3673_, v___x_3674_, v___x_3675_, v___x_3675_, v___x_3676_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
lean_dec_ref(v_fvars_3651_);
return v___x_3677_;
}
else
{
lean_dec_ref(v_fvars_3651_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3678_, lean_object* v_body_3679_, lean_object* v_x_3680_, uint8_t v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_array_push(v_fvars_3678_, v_x_3680_);
v___x_3690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3689_, v_body_3679_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
uint8_t v_a_boxed_3700_; lean_object* v_res_3701_; 
v_a_boxed_3700_ = lean_unbox(v_a_3692_);
v_res_3701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3691_, v_a_boxed_3700_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
uint8_t v_a_boxed_3711_; lean_object* v_res_3712_; 
v_a_boxed_3711_ = lean_unbox(v_a_3703_);
v_res_3712_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3702_, v_a_boxed_3711_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
uint8_t v_a_boxed_3722_; lean_object* v_res_3723_; 
v_a_boxed_3722_ = lean_unbox(v_a_3714_);
v_res_3723_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3713_, v_a_boxed_3722_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_){
_start:
{
uint8_t v_a_boxed_3733_; lean_object* v_res_3734_; 
v_a_boxed_3733_ = lean_unbox(v_a_3725_);
v_res_3734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3724_, v_a_boxed_3733_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
uint8_t v_a_boxed_3744_; lean_object* v_res_3745_; 
v_a_boxed_3744_ = lean_unbox(v_a_3736_);
v_res_3745_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3735_, v_a_boxed_3744_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3746_, lean_object* v_e_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
uint8_t v_a_boxed_3756_; lean_object* v_res_3757_; 
v_a_boxed_3756_ = lean_unbox(v_a_3748_);
v_res_3757_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3746_, v_e_3747_, v_a_boxed_3756_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
lean_dec(v_a_3754_);
lean_dec_ref(v_a_3753_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3758_, lean_object* v_e_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
uint8_t v_a_boxed_3768_; lean_object* v_res_3769_; 
v_a_boxed_3768_ = lean_unbox(v_a_3760_);
v_res_3769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3758_, v_e_3759_, v_a_boxed_3768_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3770_, lean_object* v_report_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
uint8_t v_report_boxed_3780_; uint8_t v_a_boxed_3781_; lean_object* v_res_3782_; 
v_report_boxed_3780_ = lean_unbox(v_report_3771_);
v_a_boxed_3781_ = lean_unbox(v_a_3772_);
v_res_3782_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3770_, v_report_boxed_3780_, v_a_boxed_3781_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
uint8_t v_a_boxed_3792_; lean_object* v_res_3793_; 
v_a_boxed_3792_ = lean_unbox(v_a_3784_);
v_res_3793_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3783_, v_a_boxed_3792_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3794_, lean_object* v_e_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
uint8_t v_a_boxed_3804_; lean_object* v_res_3805_; 
v_a_boxed_3804_ = lean_unbox(v_a_3796_);
v_res_3805_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3794_, v_e_3795_, v_a_boxed_3804_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3806_, lean_object* v_00_u03b1_3807_, lean_object* v_c_3808_, lean_object* v_a_3809_, lean_object* v_b_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
uint8_t v_a_boxed_3819_; lean_object* v_res_3820_; 
v_a_boxed_3819_ = lean_unbox(v_a_3811_);
v_res_3820_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3806_, v_00_u03b1_3807_, v_c_3808_, v_a_3809_, v_b_3810_, v_a_boxed_3819_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3821_, lean_object* v_00_u03b1_3822_, lean_object* v_c_3823_, lean_object* v_inst_3824_, lean_object* v_a_3825_, lean_object* v_b_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
uint8_t v_a_boxed_3835_; lean_object* v_res_3836_; 
v_a_boxed_3835_ = lean_unbox(v_a_3827_);
v_res_3836_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3821_, v_00_u03b1_3822_, v_c_3823_, v_inst_3824_, v_a_3825_, v_b_3826_, v_a_boxed_3835_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
uint8_t v_a_boxed_3846_; lean_object* v_res_3847_; 
v_a_boxed_3846_ = lean_unbox(v_a_3838_);
v_res_3847_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3837_, v_a_boxed_3846_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
uint8_t v_a_boxed_3857_; lean_object* v_res_3858_; 
v_a_boxed_3857_ = lean_unbox(v_a_3849_);
v_res_3858_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3848_, v_a_boxed_3857_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3859_, lean_object* v_prop_3860_, lean_object* v_inst_3861_, lean_object* v_e_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
uint8_t v_a_boxed_3871_; lean_object* v_res_3872_; 
v_a_boxed_3871_ = lean_unbox(v_a_3863_);
v_res_3872_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3859_, v_prop_3860_, v_inst_3861_, v_e_3862_, v_a_boxed_3871_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3873_, lean_object* v_report_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
uint8_t v_report_boxed_3883_; uint8_t v_a_boxed_3884_; lean_object* v_res_3885_; 
v_report_boxed_3883_ = lean_unbox(v_report_3874_);
v_a_boxed_3884_ = lean_unbox(v_a_3875_);
v_res_3885_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3873_, v_report_boxed_3883_, v_a_boxed_3884_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3886_, lean_object* v_prop_3887_, lean_object* v_h_3888_, lean_object* v_e_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
uint8_t v_a_boxed_3898_; lean_object* v_res_3899_; 
v_a_boxed_3898_ = lean_unbox(v_a_3890_);
v_res_3899_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3886_, v_prop_3887_, v_h_3888_, v_e_3889_, v_a_boxed_3898_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
uint8_t v_a_boxed_3909_; lean_object* v_res_3910_; 
v_a_boxed_3909_ = lean_unbox(v_a_3901_);
v_res_3910_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3900_, v_a_boxed_3909_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3911_, lean_object* v___x_3912_, lean_object* v_a_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
uint8_t v___y_62656__boxed_3923_; lean_object* v_res_3924_; 
v___y_62656__boxed_3923_ = lean_unbox(v___y_3915_);
v_res_3924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3911_, v___x_3912_, v_a_3913_, v_b_3914_, v___y_62656__boxed_3923_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v___x_3912_);
lean_dec(v_upperBound_3911_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_3925_, lean_object* v_snd_3926_, lean_object* v_a_3927_, lean_object* v___x_3928_, lean_object* v_fst_3929_, lean_object* v___x_3930_, lean_object* v_____r_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
uint8_t v___x_62720__boxed_3940_; uint8_t v___y_62723__boxed_3941_; lean_object* v_res_3942_; 
v___x_62720__boxed_3940_ = lean_unbox(v___x_3928_);
v___y_62723__boxed_3941_ = lean_unbox(v___y_3932_);
v_res_3942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_3925_, v_snd_3926_, v_a_3927_, v___x_62720__boxed_3940_, v_fst_3929_, v___x_3930_, v_____r_3931_, v___y_62723__boxed_3941_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec_ref(v___x_3930_);
lean_dec(v_a_3927_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
uint8_t v_a_boxed_3952_; lean_object* v_res_3953_; 
v_a_boxed_3952_ = lean_unbox(v_a_3944_);
v_res_3953_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_3943_, v_a_boxed_3952_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3954_, lean_object* v_prop_3955_, lean_object* v_h_3956_, lean_object* v_e_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
uint8_t v_a_boxed_3966_; lean_object* v_res_3967_; 
v_a_boxed_3966_ = lean_unbox(v_a_3958_);
v_res_3967_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3954_, v_prop_3955_, v_h_3956_, v_e_3957_, v_a_boxed_3966_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_3968_, lean_object* v_x_3969_, lean_object* v_x_3970_, lean_object* v_x_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
uint8_t v___y_62900__boxed_3980_; lean_object* v_res_3981_; 
v___y_62900__boxed_3980_ = lean_unbox(v___y_3972_);
v_res_3981_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_3968_, v_x_3969_, v_x_3970_, v_x_3971_, v___y_62900__boxed_3980_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
uint8_t v_a_boxed_3991_; lean_object* v_res_3992_; 
v_a_boxed_3991_ = lean_unbox(v_a_3983_);
v_res_3992_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3982_, v_a_boxed_3991_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3993_, uint8_t v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3993_, v___y_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
uint8_t v___y_65431__boxed_4012_; lean_object* v_res_4013_; 
v___y_65431__boxed_4012_ = lean_unbox(v___y_4004_);
v_res_4013_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4003_, v___y_65431__boxed_4012_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_4014_, uint8_t v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_4014_, v___y_4021_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
uint8_t v___y_65457__boxed_4033_; lean_object* v_res_4034_; 
v___y_65457__boxed_4033_ = lean_unbox(v___y_4025_);
v_res_4034_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4024_, v___y_65457__boxed_4033_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object* v_00_u03b1_4035_, lean_object* v_name_4036_, lean_object* v_type_4037_, lean_object* v_val_4038_, lean_object* v_k_4039_, uint8_t v_nondep_4040_, uint8_t v_kind_4041_, uint8_t v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_4036_, v_type_4037_, v_val_4038_, v_k_4039_, v_nondep_4040_, v_kind_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object* v_00_u03b1_4051_, lean_object* v_name_4052_, lean_object* v_type_4053_, lean_object* v_val_4054_, lean_object* v_k_4055_, lean_object* v_nondep_4056_, lean_object* v_kind_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v_nondep_boxed_4066_; uint8_t v_kind_boxed_4067_; uint8_t v___y_65483__boxed_4068_; lean_object* v_res_4069_; 
v_nondep_boxed_4066_ = lean_unbox(v_nondep_4056_);
v_kind_boxed_4067_ = lean_unbox(v_kind_4057_);
v___y_65483__boxed_4068_ = lean_unbox(v___y_4058_);
v_res_4069_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(v_00_u03b1_4051_, v_name_4052_, v_type_4053_, v_val_4054_, v_k_4055_, v_nondep_boxed_4066_, v_kind_boxed_4067_, v___y_65483__boxed_4068_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object* v_00_u03b1_4070_, lean_object* v_name_4071_, uint8_t v_bi_4072_, lean_object* v_type_4073_, lean_object* v_k_4074_, uint8_t v_kind_4075_, uint8_t v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_4071_, v_bi_4072_, v_type_4073_, v_k_4074_, v_kind_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object* v_00_u03b1_4085_, lean_object* v_name_4086_, lean_object* v_bi_4087_, lean_object* v_type_4088_, lean_object* v_k_4089_, lean_object* v_kind_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
uint8_t v_bi_boxed_4099_; uint8_t v_kind_boxed_4100_; uint8_t v___y_65509__boxed_4101_; lean_object* v_res_4102_; 
v_bi_boxed_4099_ = lean_unbox(v_bi_4087_);
v_kind_boxed_4100_ = lean_unbox(v_kind_4090_);
v___y_65509__boxed_4101_ = lean_unbox(v___y_4091_);
v_res_4102_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(v_00_u03b1_4085_, v_name_4086_, v_bi_boxed_4099_, v_type_4088_, v_k_4089_, v_kind_boxed_4100_, v___y_65509__boxed_4101_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4103_, lean_object* v_m_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4104_, v_a_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4107_, lean_object* v_m_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4107_, v_m_4108_, v_a_4109_);
lean_dec_ref(v_a_4109_);
lean_dec_ref(v_m_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4111_, lean_object* v_m_4112_, lean_object* v_a_4113_, lean_object* v_b_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4112_, v_a_4113_, v_b_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4116_, lean_object* v_msg_4117_, uint8_t v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4116_, v_msg_4117_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4127_, lean_object* v_msg_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
uint8_t v___y_65539__boxed_4137_; lean_object* v_res_4138_; 
v___y_65539__boxed_4137_ = lean_unbox(v___y_4129_);
v_res_4138_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4127_, v_msg_4128_, v___y_65539__boxed_4137_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4139_, lean_object* v___x_4140_, lean_object* v___x_4141_, lean_object* v_inst_4142_, lean_object* v_R_4143_, lean_object* v_a_4144_, lean_object* v_b_4145_, lean_object* v_c_4146_, uint8_t v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4139_, v___x_4141_, v_a_4144_, v_b_4145_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4156_, lean_object* v___x_4157_, lean_object* v___x_4158_, lean_object* v_inst_4159_, lean_object* v_R_4160_, lean_object* v_a_4161_, lean_object* v_b_4162_, lean_object* v_c_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
uint8_t v___y_65569__boxed_4172_; lean_object* v_res_4173_; 
v___y_65569__boxed_4172_ = lean_unbox(v___y_4164_);
v_res_4173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4156_, v___x_4157_, v___x_4158_, v_inst_4159_, v_R_4160_, v_a_4161_, v_b_4162_, v_c_4163_, v___y_65569__boxed_4172_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec_ref(v___x_4158_);
lean_dec(v___x_4157_);
lean_dec(v_upperBound_4156_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4174_, lean_object* v_a_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4175_, v_x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4178_, lean_object* v_a_4179_, lean_object* v_x_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4178_, v_a_4179_, v_x_4180_);
lean_dec(v_x_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4182_, lean_object* v_a_4183_, lean_object* v_x_4184_){
_start:
{
uint8_t v___x_4185_; 
v___x_4185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4183_, v_x_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4186_, lean_object* v_a_4187_, lean_object* v_x_4188_){
_start:
{
uint8_t v_res_4189_; lean_object* v_r_4190_; 
v_res_4189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4186_, v_a_4187_, v_x_4188_);
lean_dec(v_x_4188_);
lean_dec_ref(v_a_4187_);
v_r_4190_ = lean_box(v_res_4189_);
return v_r_4190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4191_, lean_object* v_data_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4194_, lean_object* v_a_4195_, lean_object* v_b_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4195_, v_b_4196_, v_x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object* v_00_u03b2_4199_, lean_object* v_i_4200_, lean_object* v_source_4201_, lean_object* v_target_4202_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v_i_4200_, v_source_4201_, v_target_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object* v_00_u03b2_4204_, lean_object* v_x_4205_, lean_object* v_x_4206_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_x_4205_, v_x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4208_, lean_object* v_i_4209_, lean_object* v_arg_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4208_, v_i_4209_, v_arg_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4232_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4232_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4232_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
uint8_t v___x_4221_; 
v___x_4221_ = lean_unbox(v_a_4217_);
lean_dec(v_a_4217_);
if (v___x_4221_ == 3)
{
uint8_t v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4222_ = 0;
v___x_4223_ = lean_box(v___x_4222_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4223_);
v___x_4225_ = v___x_4219_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
else
{
uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4227_ = 1;
v___x_4228_ = lean_box(v___x_4227_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4228_);
v___x_4230_ = v___x_4219_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
v_a_4233_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4216_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4216_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4241_, lean_object* v_i_4242_, lean_object* v_arg_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4241_, v_i_4242_, v_arg_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_i_4242_);
lean_dec_ref(v_pinfos_4241_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4250_, lean_object* v_opts_4251_, lean_object* v_act_4252_, lean_object* v_decl_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
lean_inc(v___y_4255_);
lean_inc_ref(v___y_4254_);
v___x_4261_ = lean_apply_6(v_act_4252_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___x_4262_ = l_Lean_profileitIOUnsafe___redArg(v_category_4250_, v_opts_4251_, v___x_4261_, v_decl_4253_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4263_, lean_object* v_opts_4264_, lean_object* v_act_4265_, lean_object* v_decl_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4263_, v_opts_4264_, v_act_4265_, v_decl_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec_ref(v_opts_4264_);
lean_dec_ref(v_category_4263_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4275_, lean_object* v_category_4276_, lean_object* v_opts_4277_, lean_object* v_act_4278_, lean_object* v_decl_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4276_, v_opts_4277_, v_act_4278_, v_decl_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_category_4289_, lean_object* v_opts_4290_, lean_object* v_act_4291_, lean_object* v_decl_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4288_, v_category_4289_, v_opts_4290_, v_act_4291_, v_decl_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_opts_4290_);
lean_dec_ref(v_category_4289_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4301_, lean_object* v_e_4302_, uint8_t v___x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___y_4312_; lean_object* v___x_4321_; uint8_t v_transparency_4322_; uint8_t v___x_4323_; 
v___x_4321_ = l_Lean_Meta_Context_config(v___y_4306_);
v_transparency_4322_ = lean_ctor_get_uint8(v___x_4321_, 9);
lean_dec_ref(v___x_4321_);
v___x_4323_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4322_, v___x_4301_);
if (v___x_4323_ == 0)
{
lean_object* v_keyedConfig_4324_; uint8_t v_trackZetaDelta_4325_; lean_object* v_zetaDeltaSet_4326_; lean_object* v_lctx_4327_; lean_object* v_localInstances_4328_; lean_object* v_defEqCtx_x3f_4329_; lean_object* v_synthPendingDepth_4330_; lean_object* v_customCanUnfoldPredicate_x3f_4331_; uint8_t v_univApprox_4332_; uint8_t v_inTypeClassResolution_4333_; uint8_t v_cacheInferType_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_keyedConfig_4324_ = lean_ctor_get(v___y_4306_, 0);
v_trackZetaDelta_4325_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7);
v_zetaDeltaSet_4326_ = lean_ctor_get(v___y_4306_, 1);
v_lctx_4327_ = lean_ctor_get(v___y_4306_, 2);
v_localInstances_4328_ = lean_ctor_get(v___y_4306_, 3);
v_defEqCtx_x3f_4329_ = lean_ctor_get(v___y_4306_, 4);
v_synthPendingDepth_4330_ = lean_ctor_get(v___y_4306_, 5);
v_customCanUnfoldPredicate_x3f_4331_ = lean_ctor_get(v___y_4306_, 6);
v_univApprox_4332_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4333_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 2);
v_cacheInferType_4334_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4324_);
v___x_4335_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4301_, v_keyedConfig_4324_);
lean_inc(v_customCanUnfoldPredicate_x3f_4331_);
lean_inc(v_synthPendingDepth_4330_);
lean_inc(v_defEqCtx_x3f_4329_);
lean_inc_ref(v_localInstances_4328_);
lean_inc_ref(v_lctx_4327_);
lean_inc(v_zetaDeltaSet_4326_);
v___x_4336_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v_zetaDeltaSet_4326_);
lean_ctor_set(v___x_4336_, 2, v_lctx_4327_);
lean_ctor_set(v___x_4336_, 3, v_localInstances_4328_);
lean_ctor_set(v___x_4336_, 4, v_defEqCtx_x3f_4329_);
lean_ctor_set(v___x_4336_, 5, v_synthPendingDepth_4330_);
lean_ctor_set(v___x_4336_, 6, v_customCanUnfoldPredicate_x3f_4331_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*7, v_trackZetaDelta_4325_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*7 + 1, v_univApprox_4332_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4333_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*7 + 3, v_cacheInferType_4334_);
v___x_4337_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4302_, v___x_4303_, v___y_4304_, v___y_4305_, v___x_4336_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec_ref_known(v___x_4336_, 7);
v___y_4312_ = v___x_4337_;
goto v___jp_4311_;
}
else
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4302_, v___x_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
v___y_4312_ = v___x_4338_;
goto v___jp_4311_;
}
v___jp_4311_:
{
if (lean_obj_tag(v___y_4312_) == 0)
{
return v___y_4312_;
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4313_ = lean_ctor_get(v___y_4312_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___y_4312_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___y_4312_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___y_4312_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4339_, lean_object* v_e_4340_, lean_object* v___x_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v___x_2117__boxed_4349_; uint8_t v___x_2118__boxed_4350_; lean_object* v_res_4351_; 
v___x_2117__boxed_4349_ = lean_unbox(v___x_4339_);
v___x_2118__boxed_4350_ = lean_unbox(v___x_4341_);
v_res_4351_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2117__boxed_4349_, v_e_4340_, v___x_2118__boxed_4350_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___f_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4358_);
v___x_4362_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4363_ = 0;
v___x_4364_ = 2;
v___x_4365_ = lean_box(v___x_4364_);
v___x_4366_ = lean_box(v___x_4363_);
v___f_4367_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4367_, 0, v___x_4365_);
lean_closure_set(v___f_4367_, 1, v_e_4353_);
lean_closure_set(v___f_4367_, 2, v___x_4366_);
v___x_4368_ = lean_box(0);
v___x_4369_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4362_, v___x_4361_, v___f_4367_, v___x_4368_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
lean_dec_ref(v___x_4361_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Meta_Sym_canon(v_e_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
return v_res_4378_;
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

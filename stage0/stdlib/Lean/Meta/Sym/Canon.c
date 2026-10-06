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
v___x_121_ = lean_array_fget_borrowed(v___y_112_, v___x_120_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Int_mkType;
v___x_125_ = lean_array_fset(v___y_112_, v___x_120_, v___x_124_);
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
lean_dec_ref(v___y_112_);
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
v___y_111_ = v_modified_141_;
v___y_112_ = v_args_140_;
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
v___y_111_ = v_modified_141_;
v___y_112_ = v_args_140_;
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
v_canon_537_ = lean_ctor_get(v___x_536_, 10);
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
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_589_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_589_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_589_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_589_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_canon_555_; lean_object* v_share_556_; lean_object* v_maxFVar_557_; lean_object* v_proofInstInfo_558_; lean_object* v_proofInstInfoFVar_559_; lean_object* v_inferType_560_; lean_object* v_getLevel_561_; lean_object* v_congrInfo_562_; lean_object* v_defEqI_563_; lean_object* v_extensions_564_; lean_object* v_issues_565_; lean_object* v_instanceOverrides_566_; uint8_t v_debug_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_588_; 
v___x_554_ = lean_st_ref_take(v_a_528_);
v_canon_555_ = lean_ctor_get(v___x_554_, 10);
v_share_556_ = lean_ctor_get(v___x_554_, 0);
v_maxFVar_557_ = lean_ctor_get(v___x_554_, 1);
v_proofInstInfo_558_ = lean_ctor_get(v___x_554_, 2);
v_proofInstInfoFVar_559_ = lean_ctor_get(v___x_554_, 3);
v_inferType_560_ = lean_ctor_get(v___x_554_, 4);
v_getLevel_561_ = lean_ctor_get(v___x_554_, 5);
v_congrInfo_562_ = lean_ctor_get(v___x_554_, 6);
v_defEqI_563_ = lean_ctor_get(v___x_554_, 7);
v_extensions_564_ = lean_ctor_get(v___x_554_, 8);
v_issues_565_ = lean_ctor_get(v___x_554_, 9);
v_instanceOverrides_566_ = lean_ctor_get(v___x_554_, 11);
v_debug_567_ = lean_ctor_get_uint8(v___x_554_, sizeof(void*)*12);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_588_ == 0)
{
v___x_569_ = v___x_554_;
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_instanceOverrides_566_);
lean_inc(v_canon_555_);
lean_inc(v_issues_565_);
lean_inc(v_extensions_564_);
lean_inc(v_defEqI_563_);
lean_inc(v_congrInfo_562_);
lean_inc(v_getLevel_561_);
lean_inc(v_inferType_560_);
lean_inc(v_proofInstInfoFVar_559_);
lean_inc(v_proofInstInfo_558_);
lean_inc(v_maxFVar_557_);
lean_inc(v_share_556_);
lean_dec(v___x_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_cache_571_; lean_object* v_cacheInType_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_587_; 
v_cache_571_ = lean_ctor_get(v_canon_555_, 0);
v_cacheInType_572_ = lean_ctor_get(v_canon_555_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_canon_555_);
if (v_isSharedCheck_587_ == 0)
{
v___x_574_ = v_canon_555_;
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_cacheInType_572_);
lean_inc(v_cache_571_);
lean_dec(v_canon_555_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_a_550_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_534_, v___x_535_, v_cache_571_, v_e_524_, v_a_550_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_cacheInType_572_);
v___x_578_ = v_reuseFailAlloc_586_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 10, v___x_578_);
v___x_580_ = v___x_569_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_share_556_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_maxFVar_557_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_proofInstInfo_558_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_proofInstInfoFVar_559_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_inferType_560_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v_getLevel_561_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_congrInfo_562_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_defEqI_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_extensions_564_);
lean_ctor_set(v_reuseFailAlloc_585_, 9, v_issues_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 10, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 11, v_instanceOverrides_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*12, v_debug_567_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_st_ref_put(v_a_528_, v___x_580_);
if (v_isShared_553_ == 0)
{
v___x_583_ = v___x_552_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_550_);
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
lean_dec_ref(v_e_524_);
return v___x_549_;
}
}
}
else
{
lean_object* v___x_590_; lean_object* v_canon_591_; lean_object* v_cacheInType_592_; lean_object* v___x_593_; 
v___x_590_ = lean_st_ref_get(v_a_528_);
v_canon_591_ = lean_ctor_get(v___x_590_, 10);
lean_inc_ref(v_canon_591_);
lean_dec(v___x_590_);
v_cacheInType_592_ = lean_ctor_get(v_canon_591_, 1);
lean_inc_ref(v_cacheInType_592_);
lean_dec_ref(v_canon_591_);
lean_inc_ref(v_e_524_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_534_, v___x_535_, v_cacheInType_592_, v_e_524_);
lean_dec_ref(v_cacheInType_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_k_525_);
lean_dec_ref(v_e_524_);
v_val_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 0);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_val_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___x_593_);
v___x_602_ = lean_box(v_a_526_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
v___x_603_ = lean_apply_8(v_k_525_, v___x_602_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_643_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_643_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_643_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_643_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v_canon_609_; lean_object* v_share_610_; lean_object* v_maxFVar_611_; lean_object* v_proofInstInfo_612_; lean_object* v_proofInstInfoFVar_613_; lean_object* v_inferType_614_; lean_object* v_getLevel_615_; lean_object* v_congrInfo_616_; lean_object* v_defEqI_617_; lean_object* v_extensions_618_; lean_object* v_issues_619_; lean_object* v_instanceOverrides_620_; uint8_t v_debug_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_642_; 
v___x_608_ = lean_st_ref_take(v_a_528_);
v_canon_609_ = lean_ctor_get(v___x_608_, 10);
v_share_610_ = lean_ctor_get(v___x_608_, 0);
v_maxFVar_611_ = lean_ctor_get(v___x_608_, 1);
v_proofInstInfo_612_ = lean_ctor_get(v___x_608_, 2);
v_proofInstInfoFVar_613_ = lean_ctor_get(v___x_608_, 3);
v_inferType_614_ = lean_ctor_get(v___x_608_, 4);
v_getLevel_615_ = lean_ctor_get(v___x_608_, 5);
v_congrInfo_616_ = lean_ctor_get(v___x_608_, 6);
v_defEqI_617_ = lean_ctor_get(v___x_608_, 7);
v_extensions_618_ = lean_ctor_get(v___x_608_, 8);
v_issues_619_ = lean_ctor_get(v___x_608_, 9);
v_instanceOverrides_620_ = lean_ctor_get(v___x_608_, 11);
v_debug_621_ = lean_ctor_get_uint8(v___x_608_, sizeof(void*)*12);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_642_ == 0)
{
v___x_623_ = v___x_608_;
v_isShared_624_ = v_isSharedCheck_642_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_instanceOverrides_620_);
lean_inc(v_canon_609_);
lean_inc(v_issues_619_);
lean_inc(v_extensions_618_);
lean_inc(v_defEqI_617_);
lean_inc(v_congrInfo_616_);
lean_inc(v_getLevel_615_);
lean_inc(v_inferType_614_);
lean_inc(v_proofInstInfoFVar_613_);
lean_inc(v_proofInstInfo_612_);
lean_inc(v_maxFVar_611_);
lean_inc(v_share_610_);
lean_dec(v___x_608_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_642_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_cache_625_; lean_object* v_cacheInType_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_641_; 
v_cache_625_ = lean_ctor_get(v_canon_609_, 0);
v_cacheInType_626_ = lean_ctor_get(v_canon_609_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_canon_609_);
if (v_isSharedCheck_641_ == 0)
{
v___x_628_ = v_canon_609_;
v_isShared_629_ = v_isSharedCheck_641_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_cacheInType_626_);
lean_inc(v_cache_625_);
lean_dec(v_canon_609_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_641_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
lean_inc(v_a_604_);
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_534_, v___x_535_, v_cacheInType_626_, v_e_524_, v_a_604_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_cache_625_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_640_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 10, v___x_632_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_share_610_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_maxFVar_611_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_proofInstInfo_612_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_proofInstInfoFVar_613_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_inferType_614_);
lean_ctor_set(v_reuseFailAlloc_639_, 5, v_getLevel_615_);
lean_ctor_set(v_reuseFailAlloc_639_, 6, v_congrInfo_616_);
lean_ctor_set(v_reuseFailAlloc_639_, 7, v_defEqI_617_);
lean_ctor_set(v_reuseFailAlloc_639_, 8, v_extensions_618_);
lean_ctor_set(v_reuseFailAlloc_639_, 9, v_issues_619_);
lean_ctor_set(v_reuseFailAlloc_639_, 10, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_639_, 11, v_instanceOverrides_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*12, v_debug_621_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_st_ref_put(v_a_528_, v___x_634_);
if (v_isShared_607_ == 0)
{
v___x_637_ = v___x_606_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_604_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
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
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_644_, lean_object* v_k_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
uint8_t v_a_boxed_654_; lean_object* v_res_655_; 
v_a_boxed_654_ = lean_unbox(v_a_646_);
v_res_655_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_644_, v_k_645_, v_a_boxed_654_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = l_Lean_Expr_cleanupAnnotations(v_e_662_);
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_665_ = l_Lean_Expr_isConstOf(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_663_);
return v___x_666_;
}
else
{
lean_object* v_arg_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_arg_667_ = lean_ctor_get(v___x_663_, 1);
lean_inc_ref(v_arg_667_);
v___x_668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_669_ = l_Lean_Expr_isApp(v___x_668_);
if (v___x_669_ == 0)
{
lean_dec_ref(v___x_668_);
lean_dec_ref(v_arg_667_);
return v___x_669_;
}
else
{
lean_object* v_arg_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_arg_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc_ref(v_arg_670_);
v___x_671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_668_);
v___x_672_ = l_Lean_Expr_isApp(v___x_671_);
if (v___x_672_ == 0)
{
lean_dec_ref(v___x_671_);
lean_dec_ref(v_arg_670_);
lean_dec_ref(v_arg_667_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = l_Lean_Expr_appFnCleanup___redArg(v___x_671_);
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_675_ = l_Lean_Expr_isConstOf(v___x_673_, v___x_674_);
lean_dec_ref(v___x_673_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_arg_670_);
lean_dec_ref(v_arg_667_);
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_Expr_isBoolTrue(v_arg_670_);
if (v___x_676_ == 0)
{
lean_dec_ref(v_arg_667_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_Expr_isBoolTrue(v_arg_667_);
return v___x_677_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_663_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = l_Lean_Expr_cleanupAnnotations(v_e_684_);
v___x_686_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_687_ = l_Lean_Expr_isConstOf(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_Expr_isApp(v___x_685_);
if (v___x_688_ == 0)
{
lean_dec_ref(v___x_685_);
return v___x_688_;
}
else
{
lean_object* v_arg_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_arg_689_ = lean_ctor_get(v___x_685_, 1);
lean_inc_ref(v_arg_689_);
v___x_690_ = l_Lean_Expr_appFnCleanup___redArg(v___x_685_);
v___x_691_ = l_Lean_Expr_isApp(v___x_690_);
if (v___x_691_ == 0)
{
lean_dec_ref(v___x_690_);
lean_dec_ref(v_arg_689_);
return v___x_691_;
}
else
{
lean_object* v_arg_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_arg_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc_ref(v_arg_692_);
v___x_693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_690_);
v___x_694_ = l_Lean_Expr_isApp(v___x_693_);
if (v___x_694_ == 0)
{
lean_dec_ref(v___x_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_689_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = l_Lean_Expr_appFnCleanup___redArg(v___x_693_);
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_697_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_696_);
lean_dec_ref(v___x_695_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_689_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Expr_isBoolFalse(v_arg_692_);
if (v___x_698_ == 0)
{
lean_dec_ref(v_arg_689_);
return v___x_698_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Expr_isBoolTrue(v_arg_689_);
return v___x_699_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_685_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t v_x_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(v_x_703_);
v___x_705_ = lean_obj_tag_nat(v___x_704_);
lean_dec(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object* v_x_706_){
_start:
{
uint8_t v_x_4__boxed_707_; lean_object* v_res_708_; 
v_x_4__boxed_707_ = lean_unbox(v_x_706_);
v_res_708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_4__boxed_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_709_){
_start:
{
lean_inc(v_k_709_);
return v_k_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_710_);
lean_dec(v_k_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_712_, lean_object* v_ctorIdx_713_, uint8_t v_t_714_, lean_object* v_h_715_, lean_object* v_k_716_){
_start:
{
lean_inc(v_k_716_);
return v_k_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_717_, lean_object* v_ctorIdx_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_k_721_){
_start:
{
uint8_t v_t_boxed_722_; lean_object* v_res_723_; 
v_t_boxed_722_ = lean_unbox(v_t_719_);
v_res_723_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_717_, v_ctorIdx_718_, v_t_boxed_722_, v_h_720_, v_k_721_);
lean_dec(v_k_721_);
lean_dec(v_ctorIdx_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_724_){
_start:
{
lean_inc(v_canonType_724_);
return v_canonType_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_725_);
lean_dec(v_canonType_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_727_, uint8_t v_t_728_, lean_object* v_h_729_, lean_object* v_canonType_730_){
_start:
{
lean_inc(v_canonType_730_);
return v_canonType_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_731_, lean_object* v_t_732_, lean_object* v_h_733_, lean_object* v_canonType_734_){
_start:
{
uint8_t v_t_boxed_735_; lean_object* v_res_736_; 
v_t_boxed_735_ = lean_unbox(v_t_732_);
v_res_736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_731_, v_t_boxed_735_, v_h_733_, v_canonType_734_);
lean_dec(v_canonType_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_737_){
_start:
{
lean_inc(v_canonInst_737_);
return v_canonInst_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_738_);
lean_dec(v_canonInst_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_740_, uint8_t v_t_741_, lean_object* v_h_742_, lean_object* v_canonInst_743_){
_start:
{
lean_inc(v_canonInst_743_);
return v_canonInst_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_744_, lean_object* v_t_745_, lean_object* v_h_746_, lean_object* v_canonInst_747_){
_start:
{
uint8_t v_t_boxed_748_; lean_object* v_res_749_; 
v_t_boxed_748_ = lean_unbox(v_t_745_);
v_res_749_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_744_, v_t_boxed_748_, v_h_746_, v_canonInst_747_);
lean_dec(v_canonInst_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_750_){
_start:
{
lean_inc(v_canonImplicit_750_);
return v_canonImplicit_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_751_);
lean_dec(v_canonImplicit_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_753_, uint8_t v_t_754_, lean_object* v_h_755_, lean_object* v_canonImplicit_756_){
_start:
{
lean_inc(v_canonImplicit_756_);
return v_canonImplicit_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_canonImplicit_760_){
_start:
{
uint8_t v_t_boxed_761_; lean_object* v_res_762_; 
v_t_boxed_761_ = lean_unbox(v_t_758_);
v_res_762_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_757_, v_t_boxed_761_, v_h_759_, v_canonImplicit_760_);
lean_dec(v_canonImplicit_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_763_){
_start:
{
lean_inc(v_visit_763_);
return v_visit_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_764_);
lean_dec(v_visit_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_766_, uint8_t v_t_767_, lean_object* v_h_768_, lean_object* v_visit_769_){
_start:
{
lean_inc(v_visit_769_);
return v_visit_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_770_, lean_object* v_t_771_, lean_object* v_h_772_, lean_object* v_visit_773_){
_start:
{
uint8_t v_t_boxed_774_; lean_object* v_res_775_; 
v_t_boxed_774_ = lean_unbox(v_t_771_);
v_res_775_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_770_, v_t_boxed_774_, v_h_772_, v_visit_773_);
lean_dec(v_visit_773_);
return v_res_775_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_790_, lean_object* v_x_791_){
_start:
{
switch(v_r_790_)
{
case 0:
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_792_;
}
case 1:
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_793_;
}
case 2:
{
lean_object* v___x_794_; 
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_794_;
}
default: 
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_r_boxed_798_; lean_object* v_res_799_; 
v_r_boxed_798_ = lean_unbox(v_r_796_);
v_res_799_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_798_, v_x_797_);
lean_dec(v_x_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_802_, lean_object* v_i_803_, lean_object* v_arg_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_array_get_size(v_pinfos_802_);
v___x_861_ = lean_nat_dec_lt(v_i_803_, v___x_860_);
if (v___x_861_ == 0)
{
v___y_811_ = v_a_805_;
v___y_812_ = v_a_806_;
v___y_813_ = v_a_807_;
v___y_814_ = v_a_808_;
goto v___jp_810_;
}
else
{
lean_object* v_pinfo_862_; uint8_t v_isInstance_863_; 
v_pinfo_862_ = lean_array_fget_borrowed(v_pinfos_802_, v_i_803_);
v_isInstance_863_ = lean_ctor_get_uint8(v_pinfo_862_, sizeof(void*)*1 + 4);
if (v_isInstance_863_ == 0)
{
uint8_t v_isProp_864_; 
v_isProp_864_ = lean_ctor_get_uint8(v_pinfo_862_, sizeof(void*)*1 + 2);
if (v_isProp_864_ == 0)
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_862_);
if (v___x_865_ == 0)
{
v___y_811_ = v_a_805_;
v___y_812_ = v_a_806_;
v___y_813_ = v_a_807_;
v___y_814_ = v_a_808_;
goto v___jp_810_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_isTypeFormer(v_arg_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_882_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_882_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
uint8_t v___x_871_; 
v___x_871_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = 2;
v___x_873_ = lean_box(v___x_872_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = 0;
v___x_878_ = lean_box(v___x_877_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_878_);
v___x_880_ = v___x_869_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_866_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_866_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
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
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_arg_804_);
v___x_891_ = 3;
v___x_892_ = lean_box(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
else
{
uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_arg_804_);
v___x_894_ = 1;
v___x_895_ = lean_box(v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
v___jp_810_:
{
lean_object* v___x_815_; 
lean_inc_ref(v_arg_804_);
v___x_815_ = l_Lean_Meta_isProp(v_arg_804_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_851_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_851_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_851_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_851_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v___x_820_; 
v___x_820_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_del_object(v___x_818_);
v___x_821_ = l_Lean_Meta_isTypeFormer(v_arg_804_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_837_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_837_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v___x_826_; 
v___x_826_ = lean_unbox(v_a_822_);
lean_dec(v_a_822_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = 3;
v___x_828_ = lean_box(v___x_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = 0;
v___x_833_ = lean_box(v___x_832_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_833_);
v___x_835_ = v___x_824_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_821_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_821_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec_ref(v_arg_804_);
v___x_846_ = 3;
v___x_847_ = lean_box(v___x_846_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_847_);
v___x_849_ = v___x_818_;
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
lean_dec_ref(v_arg_804_);
v_a_852_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_815_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_815_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_897_, lean_object* v_i_898_, lean_object* v_arg_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_897_, v_i_898_, v_arg_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_i_898_);
lean_dec_ref(v_pinfos_897_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_906_, lean_object* v_offset_907_){
_start:
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_dec_eq(v_offset_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Lean_mkNatLit(v_offset_907_);
v___x_911_ = l_Lean_mkNatAdd(v_e_906_, v___x_910_);
return v___x_911_;
}
else
{
lean_dec(v_offset_907_);
return v_e_906_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_912_; lean_object* v_dummy_913_; 
v___x_912_ = lean_box(0);
v_dummy_913_ = l_Lean_Expr_sort___override(v___x_912_);
return v_dummy_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_914_, lean_object* v_e_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_fromClass_921_; 
v_fromClass_921_ = lean_ctor_get_uint8(v_info_914_, sizeof(void*)*3);
if (v_fromClass_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_915_, v_fromClass_921_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_958_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_958_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_958_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_958_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 1)
{
lean_object* v_val_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_del_object(v___x_925_);
v_val_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v_a_923_, 1);
v___x_928_ = l_Lean_Expr_getAppFn(v_val_927_);
v___x_929_ = l_Lean_Meta_reduceProj_x3f(v___x_928_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
if (lean_obj_tag(v_a_930_) == 0)
{
lean_dec(v_val_927_);
return v___x_929_;
}
else
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_952_; 
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_953_);
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_952_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_952_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_951_; 
v_val_934_ = lean_ctor_get(v_a_930_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_951_ == 0)
{
v___x_936_ = v_a_930_;
v_isShared_937_ = v_isSharedCheck_951_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v_a_930_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_951_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_dummy_938_; lean_object* v_nargs_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v_dummy_938_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_939_ = l_Lean_Expr_getAppNumArgs(v_val_927_);
lean_inc(v_nargs_939_);
v___x_940_ = lean_mk_array(v_nargs_939_, v_dummy_938_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_sub(v_nargs_939_, v___x_941_);
lean_dec(v_nargs_939_);
v___x_943_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_927_, v___x_940_, v___x_942_);
v___x_944_ = l_Lean_mkAppN(v_val_934_, v___x_943_);
lean_dec_ref(v___x_943_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_946_);
v___x_948_ = v___x_932_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
else
{
lean_dec(v_val_927_);
return v___x_929_;
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_956_; 
lean_dec(v_a_923_);
v___x_954_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_954_);
v___x_956_ = v___x_925_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
return v___x_922_;
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v_e_915_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_961_, lean_object* v_e_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_961_, v_e_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_info_961_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_969_, lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_969_, v_e_970_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_979_, lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_979_, v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec_ref(v_info_979_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_989_){
_start:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_991_ = l_Lean_Expr_isConstOf(v_e_989_, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_992_);
lean_dec_ref(v_e_992_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1029_ = l_Lean_Expr_cleanupAnnotations(v_e_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_1031_ = l_Lean_Expr_isConstOf(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; 
v___x_1032_ = l_Lean_Expr_isApp(v___x_1029_);
if (v___x_1032_ == 0)
{
lean_dec_ref(v___x_1029_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1029_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_1035_ = l_Lean_Expr_isConstOf(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Lean_Expr_isApp(v___x_1033_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v___x_1033_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1033_);
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
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1041_);
v___x_1044_ = l_Lean_Expr_isApp(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec_ref(v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_arg_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_arg_1045_ = lean_ctor_get(v___x_1043_, 1);
lean_inc_ref(v_arg_1045_);
v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1043_);
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1048_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1050_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1052_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1054_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1056_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1055_);
lean_dec_ref(v___x_1046_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v_arg_1045_);
return v___x_1056_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1045_);
lean_dec_ref(v_arg_1045_);
return v___x_1057_;
}
}
else
{
uint8_t v___x_1058_; 
lean_dec_ref(v___x_1046_);
v___x_1058_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1045_);
lean_dec_ref(v_arg_1045_);
return v___x_1058_;
}
}
else
{
uint8_t v___x_1059_; 
lean_dec_ref(v___x_1046_);
v___x_1059_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1045_);
lean_dec_ref(v_arg_1045_);
return v___x_1059_;
}
}
else
{
uint8_t v___x_1060_; 
lean_dec_ref(v___x_1046_);
v___x_1060_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1045_);
lean_dec_ref(v_arg_1045_);
return v___x_1060_;
}
}
else
{
uint8_t v___x_1061_; 
lean_dec_ref(v___x_1046_);
v___x_1061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1045_);
lean_dec_ref(v_arg_1045_);
return v___x_1061_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1033_);
return v___x_1035_;
}
}
}
else
{
lean_dec_ref(v___x_1029_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1062_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1071_, lean_object* v_inst_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; 
lean_inc_ref(v_inst_1072_);
lean_inc_ref(v_e_1071_);
v___x_1080_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1071_, v_inst_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1131_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1131_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1131_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_unbox(v_a_1081_);
lean_dec(v_a_1081_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1083_);
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1071_);
v___x_1087_ = l_Lean_indentExpr(v_e_1071_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_indentExpr(v_inst_1072_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1073_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1119_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1119_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1119_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v_verbose_1098_; 
v_verbose_1098_ = lean_ctor_get_uint8(v_a_1094_, 0);
lean_dec(v_a_1094_);
if (v_verbose_1098_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref_known(v___x_1092_, 2);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_e_1071_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_e_1071_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v___x_1102_; 
lean_del_object(v___x_1096_);
v___x_1102_ = l_Lean_Meta_Sym_reportIssue(v___x_1092_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v___x_1102_, 0);
lean_dec(v_unused_1110_);
v___x_1104_ = v___x_1102_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v___x_1102_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_e_1071_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_e_1071_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_e_1071_);
v_a_1111_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1102_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1102_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref_known(v___x_1092_, 2);
lean_dec_ref(v_e_1071_);
v_a_1120_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1093_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1093_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v_e_1071_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_inst_1072_);
v___x_1129_ = v___x_1083_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_inst_1072_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_e_1071_);
v_a_1132_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1080_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1080_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1140_, lean_object* v_inst_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1140_, v_inst_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_1153_, lean_object* v_type_1154_, uint8_t v_report_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; 
lean_inc_ref(v_type_1154_);
v___x_1163_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1154_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1215_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1215_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1215_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
if (lean_obj_tag(v_a_1164_) == 1)
{
lean_object* v_val_1168_; lean_object* v___x_1169_; 
lean_del_object(v___x_1166_);
lean_dec_ref(v_type_1154_);
v_val_1168_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_a_1164_, 1);
v___x_1169_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1153_, v_val_1168_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1169_;
}
else
{
lean_dec(v_a_1164_);
if (v_report_1155_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v_type_1154_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_e_1153_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_e_1153_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_del_object(v___x_1166_);
v___x_1173_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1153_);
v___x_1174_ = l_Lean_indentExpr(v_e_1153_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_indentExpr(v_type_1154_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1156_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1206_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1206_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1206_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint8_t v_verbose_1185_; 
v_verbose_1185_ = lean_ctor_get_uint8(v_a_1181_, 0);
lean_dec(v_a_1181_);
if (v_verbose_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1179_, 2);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v_e_1153_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_e_1153_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
lean_object* v___x_1189_; 
lean_del_object(v___x_1183_);
v___x_1189_ = l_Lean_Meta_Sym_reportIssue(v___x_1179_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1197_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_e_1153_);
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_e_1153_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_e_1153_);
v_a_1198_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1189_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1189_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref_known(v___x_1179_, 2);
lean_dec_ref(v_e_1153_);
v_a_1207_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1180_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1180_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_type_1154_);
lean_dec_ref(v_e_1153_);
v_a_1216_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1163_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1163_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1224_, lean_object* v_type_1225_, lean_object* v_report_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
uint8_t v_report_boxed_1234_; lean_object* v_res_1235_; 
v_report_boxed_1234_ = lean_unbox(v_report_1226_);
v_res_1235_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1224_, v_type_1225_, v_report_boxed_1234_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1236_, lean_object* v_type_1237_, uint8_t v_report_1238_, uint8_t v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1236_, v_type_1237_, v_report_1238_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1248_, lean_object* v_type_1249_, lean_object* v_report_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_report_boxed_1259_; uint8_t v_a_boxed_1260_; lean_object* v_res_1261_; 
v_report_boxed_1259_ = lean_unbox(v_report_1250_);
v_a_boxed_1260_ = lean_unbox(v_a_1251_);
v_res_1261_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1248_, v_type_1249_, v_report_boxed_1259_, v_a_boxed_1260_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1261_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1262_, lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1263_) == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
return v___x_1264_;
}
else
{
lean_object* v_key_1265_; lean_object* v_tail_1266_; uint8_t v___x_1267_; 
v_key_1265_ = lean_ctor_get(v_x_1263_, 0);
v_tail_1266_ = lean_ctor_get(v_x_1263_, 2);
v___x_1267_ = lean_expr_eqv(v_key_1265_, v_a_1262_);
if (v___x_1267_ == 0)
{
v_x_1263_ = v_tail_1266_;
goto _start;
}
else
{
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec_ref(v_a_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
if (lean_obj_tag(v_x_1274_) == 0)
{
return v_x_1273_;
}
else
{
lean_object* v_key_1275_; lean_object* v_value_1276_; lean_object* v_tail_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1300_; 
v_key_1275_ = lean_ctor_get(v_x_1274_, 0);
v_value_1276_ = lean_ctor_get(v_x_1274_, 1);
v_tail_1277_ = lean_ctor_get(v_x_1274_, 2);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1279_ = v_x_1274_;
v_isShared_1280_ = v_isSharedCheck_1300_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_tail_1277_);
lean_inc(v_value_1276_);
lean_inc(v_key_1275_);
lean_dec(v_x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1300_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v_fold_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1281_ = lean_array_get_size(v_x_1273_);
v___x_1282_ = l_Lean_Expr_hash(v_key_1275_);
v___x_1283_ = 32ULL;
v___x_1284_ = lean_uint64_shift_right(v___x_1282_, v___x_1283_);
v_fold_1285_ = lean_uint64_xor(v___x_1282_, v___x_1284_);
v___x_1286_ = 16ULL;
v___x_1287_ = lean_uint64_shift_right(v_fold_1285_, v___x_1286_);
v___x_1288_ = lean_uint64_xor(v_fold_1285_, v___x_1287_);
v___x_1289_ = lean_uint64_to_usize(v___x_1288_);
v___x_1290_ = lean_usize_of_nat(v___x_1281_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_sub(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_usize_land(v___x_1289_, v___x_1292_);
v___x_1294_ = lean_array_uget_borrowed(v_x_1273_, v___x_1293_);
lean_inc(v___x_1294_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 2, v___x_1294_);
v___x_1296_ = v___x_1279_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_key_1275_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_value_1276_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_array_uset(v_x_1273_, v___x_1293_, v___x_1296_);
v_x_1273_ = v___x_1297_;
v_x_1274_ = v_tail_1277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(lean_object* v_i_1301_, lean_object* v_source_1302_, lean_object* v_target_1303_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_array_get_size(v_source_1302_);
v___x_1305_ = lean_nat_dec_lt(v_i_1301_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_source_1302_);
lean_dec(v_i_1301_);
return v_target_1303_;
}
else
{
lean_object* v_es_1306_; lean_object* v___x_1307_; lean_object* v_source_1308_; lean_object* v_target_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_es_1306_ = lean_array_fget(v_source_1302_, v_i_1301_);
v___x_1307_ = lean_box(0);
v_source_1308_ = lean_array_fset(v_source_1302_, v_i_1301_, v___x_1307_);
v_target_1309_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_target_1303_, v_es_1306_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v_i_1301_, v___x_1310_);
lean_dec(v_i_1301_);
v_i_1301_ = v___x_1311_;
v_source_1302_ = v_source_1308_;
v_target_1303_ = v_target_1309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_nbuckets_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1314_ = lean_array_get_size(v_data_1313_);
v___x_1315_ = lean_unsigned_to_nat(2u);
v_nbuckets_1316_ = lean_nat_mul(v___x_1314_, v___x_1315_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_mk_array(v_nbuckets_1316_, v___x_1318_);
v___x_1320_ = lean_array_propagate_mark(v_data_1313_, v___x_1319_);
v___x_1321_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v___x_1317_, v_data_1313_, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_x_1324_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_dec(v_b_1323_);
lean_dec_ref(v_a_1322_);
return v_x_1324_;
}
else
{
lean_object* v_key_1325_; lean_object* v_value_1326_; lean_object* v_tail_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1339_; 
v_key_1325_ = lean_ctor_get(v_x_1324_, 0);
v_value_1326_ = lean_ctor_get(v_x_1324_, 1);
v_tail_1327_ = lean_ctor_get(v_x_1324_, 2);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1329_ = v_x_1324_;
v_isShared_1330_ = v_isSharedCheck_1339_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_tail_1327_);
lean_inc(v_value_1326_);
lean_inc(v_key_1325_);
lean_dec(v_x_1324_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1339_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_expr_eqv(v_key_1325_, v_a_1322_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1322_, v_b_1323_, v_tail_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 2, v___x_1332_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_key_1325_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_value_1326_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_value_1326_);
lean_dec(v_key_1325_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v_b_1323_);
lean_ctor_set(v___x_1329_, 0, v_a_1322_);
v___x_1337_ = v___x_1329_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1322_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_b_1323_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_tail_1327_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1340_, lean_object* v_a_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v_size_1343_; lean_object* v_buckets_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1387_; 
v_size_1343_ = lean_ctor_get(v_m_1340_, 0);
v_buckets_1344_ = lean_ctor_get(v_m_1340_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_m_1340_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1346_ = v_m_1340_;
v_isShared_1347_ = v_isSharedCheck_1387_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_buckets_1344_);
lean_inc(v_size_1343_);
lean_dec(v_m_1340_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1387_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v_fold_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v_bkt_1361_; uint8_t v___x_1362_; 
v___x_1348_ = lean_array_get_size(v_buckets_1344_);
v___x_1349_ = l_Lean_Expr_hash(v_a_1341_);
v___x_1350_ = 32ULL;
v___x_1351_ = lean_uint64_shift_right(v___x_1349_, v___x_1350_);
v_fold_1352_ = lean_uint64_xor(v___x_1349_, v___x_1351_);
v___x_1353_ = 16ULL;
v___x_1354_ = lean_uint64_shift_right(v_fold_1352_, v___x_1353_);
v___x_1355_ = lean_uint64_xor(v_fold_1352_, v___x_1354_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = lean_usize_of_nat(v___x_1348_);
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_sub(v___x_1357_, v___x_1358_);
v___x_1360_ = lean_usize_land(v___x_1356_, v___x_1359_);
v_bkt_1361_ = lean_array_uget_borrowed(v_buckets_1344_, v___x_1360_);
v___x_1362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1341_, v_bkt_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v_size_x27_1364_; lean_object* v___x_1365_; lean_object* v_buckets_x27_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v_size_x27_1364_ = lean_nat_add(v_size_1343_, v___x_1363_);
lean_dec(v_size_1343_);
lean_inc(v_bkt_1361_);
v___x_1365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1341_);
lean_ctor_set(v___x_1365_, 1, v_b_1342_);
lean_ctor_set(v___x_1365_, 2, v_bkt_1361_);
v_buckets_x27_1366_ = lean_array_uset(v_buckets_1344_, v___x_1360_, v___x_1365_);
v___x_1367_ = lean_unsigned_to_nat(4u);
v___x_1368_ = lean_nat_mul(v_size_x27_1364_, v___x_1367_);
v___x_1369_ = lean_unsigned_to_nat(3u);
v___x_1370_ = lean_nat_div(v___x_1368_, v___x_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_array_get_size(v_buckets_x27_1366_);
v___x_1372_ = lean_nat_dec_le(v___x_1370_, v___x_1371_);
lean_dec(v___x_1370_);
if (v___x_1372_ == 0)
{
lean_object* v_val_1373_; lean_object* v___x_1375_; 
v_val_1373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1366_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_val_1373_);
lean_ctor_set(v___x_1346_, 0, v_size_x27_1364_);
v___x_1375_ = v___x_1346_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_size_x27_1364_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_val_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1378_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_buckets_x27_1366_);
lean_ctor_set(v___x_1346_, 0, v_size_x27_1364_);
v___x_1378_ = v___x_1346_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_size_x27_1364_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_buckets_x27_1366_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v_buckets_x27_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_inc(v_bkt_1361_);
v___x_1380_ = lean_box(0);
v_buckets_x27_1381_ = lean_array_uset(v_buckets_1344_, v___x_1360_, v___x_1380_);
v___x_1382_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1341_, v_b_1342_, v_bkt_1361_);
v___x_1383_ = lean_array_uset(v_buckets_x27_1381_, v___x_1360_, v___x_1382_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1383_);
v___x_1385_ = v___x_1346_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_size_1343_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(lean_object* v_k_1388_, uint8_t v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(v___y_1389_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
v___x_1399_ = lean_apply_9(v_k_1388_, v_b_1392_, v___x_1398_, v___y_1390_, v___y_1391_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed(lean_object* v_k_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v___y_61796__boxed_1410_; lean_object* v_res_1411_; 
v___y_61796__boxed_1410_ = lean_unbox(v___y_1401_);
v_res_1411_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0(v_k_1400_, v___y_61796__boxed_1410_, v___y_1402_, v___y_1403_, v_b_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(lean_object* v_name_1412_, uint8_t v_bi_1413_, lean_object* v_type_1414_, lean_object* v_k_1415_, uint8_t v_kind_1416_, uint8_t v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(v___y_1417_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1426_, 0, v_k_1415_);
lean_closure_set(v___f_1426_, 1, v___x_1425_);
lean_closure_set(v___f_1426_, 2, v___y_1418_);
lean_closure_set(v___f_1426_, 3, v___y_1419_);
v___x_1427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1412_, v_bi_1413_, v_type_1414_, v___f_1426_, v_kind_1416_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1427_) == 0)
{
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg___boxed(lean_object* v_name_1436_, lean_object* v_bi_1437_, lean_object* v_type_1438_, lean_object* v_k_1439_, lean_object* v_kind_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_bi_boxed_1449_; uint8_t v_kind_boxed_1450_; uint8_t v___y_61824__boxed_1451_; lean_object* v_res_1452_; 
v_bi_boxed_1449_ = lean_unbox(v_bi_1437_);
v_kind_boxed_1450_ = lean_unbox(v_kind_1440_);
v___y_61824__boxed_1451_ = lean_unbox(v___y_1441_);
v_res_1452_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_1436_, v_bi_boxed_1449_, v_type_1438_, v_k_1439_, v_kind_boxed_1450_, v___y_61824__boxed_1451_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v_env_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = lean_st_ref_get(v___y_1454_);
v_env_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_Meta_isMatcherCore(v_env_1457_, v_declName_1453_);
v___x_1459_ = lean_box(v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1461_, v___y_1462_);
lean_dec(v___y_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(lean_object* v_msgData_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v_env_1472_; uint8_t v___x_1473_; lean_object* v_env_1474_; lean_object* v___x_1475_; lean_object* v_toCold_1476_; lean_object* v_mctx_1477_; lean_object* v_lctx_1478_; lean_object* v_options_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1471_ = lean_st_ref_get(v___y_1469_);
v_env_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc_ref(v_env_1472_);
lean_dec(v___x_1471_);
v___x_1473_ = 0;
v_env_1474_ = l_Lean_Environment_setRecordingDeps(v_env_1472_, v___x_1473_);
v___x_1475_ = lean_st_ref_get(v___y_1467_);
v_toCold_1476_ = lean_ctor_get(v___y_1468_, 0);
v_mctx_1477_ = lean_ctor_get(v___x_1475_, 0);
lean_inc_ref(v_mctx_1477_);
lean_dec(v___x_1475_);
v_lctx_1478_ = lean_ctor_get(v___y_1466_, 2);
v_options_1479_ = lean_ctor_get(v_toCold_1476_, 2);
lean_inc_ref(v_options_1479_);
lean_inc_ref(v_lctx_1478_);
v___x_1480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1480_, 0, v_env_1474_);
lean_ctor_set(v___x_1480_, 1, v_mctx_1477_);
lean_ctor_set(v___x_1480_, 2, v_lctx_1478_);
lean_ctor_set(v___x_1480_, 3, v_options_1479_);
v___x_1481_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_msgData_1465_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23___boxed(lean_object* v_msgData_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msgData_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1489_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1490_; double v___x_1491_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_float_of_nat(v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1495_, lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_ref_1502_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1549_; 
v_ref_1502_ = lean_ctor_get(v___y_1499_, 2);
v___x_1503_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__23(v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1549_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1549_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v_traceState_1509_; lean_object* v_env_1510_; lean_object* v_nextMacroScope_1511_; lean_object* v_ngen_1512_; lean_object* v_auxDeclNGen_1513_; lean_object* v_cache_1514_; lean_object* v_recordedDeps_1515_; lean_object* v_messages_1516_; lean_object* v_infoState_1517_; lean_object* v_snapshotTasks_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1548_; 
v___x_1508_ = lean_st_ref_take(v___y_1500_);
v_traceState_1509_ = lean_ctor_get(v___x_1508_, 4);
v_env_1510_ = lean_ctor_get(v___x_1508_, 0);
v_nextMacroScope_1511_ = lean_ctor_get(v___x_1508_, 1);
v_ngen_1512_ = lean_ctor_get(v___x_1508_, 2);
v_auxDeclNGen_1513_ = lean_ctor_get(v___x_1508_, 3);
v_cache_1514_ = lean_ctor_get(v___x_1508_, 5);
v_recordedDeps_1515_ = lean_ctor_get(v___x_1508_, 6);
v_messages_1516_ = lean_ctor_get(v___x_1508_, 7);
v_infoState_1517_ = lean_ctor_get(v___x_1508_, 8);
v_snapshotTasks_1518_ = lean_ctor_get(v___x_1508_, 9);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1520_ = v___x_1508_;
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snapshotTasks_1518_);
lean_inc(v_infoState_1517_);
lean_inc(v_messages_1516_);
lean_inc(v_recordedDeps_1515_);
lean_inc(v_cache_1514_);
lean_inc(v_traceState_1509_);
lean_inc(v_auxDeclNGen_1513_);
lean_inc(v_ngen_1512_);
lean_inc(v_nextMacroScope_1511_);
lean_inc(v_env_1510_);
lean_dec(v___x_1508_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint64_t v_tid_1522_; lean_object* v_traces_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1547_; 
v_tid_1522_ = lean_ctor_get_uint64(v_traceState_1509_, sizeof(void*)*1);
v_traces_1523_ = lean_ctor_get(v_traceState_1509_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_traceState_1509_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1525_ = v_traceState_1509_;
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_traces_1523_);
lean_dec(v_traceState_1509_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; double v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1530_ = 0;
v___x_1531_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1532_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1532_, 0, v_cls_1495_);
lean_ctor_set(v___x_1532_, 1, v___x_1528_);
lean_ctor_set(v___x_1532_, 2, v___x_1531_);
lean_ctor_set_float(v___x_1532_, sizeof(void*)*3, v___x_1529_);
lean_ctor_set_float(v___x_1532_, sizeof(void*)*3 + 8, v___x_1529_);
lean_ctor_set_uint8(v___x_1532_, sizeof(void*)*3 + 16, v___x_1530_);
v___x_1533_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1534_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v_a_1504_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_inc(v_ref_1502_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_ref_1502_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = l_Lean_PersistentArray_push___redArg(v_traces_1523_, v___x_1535_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1536_);
v___x_1538_ = v___x_1525_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1536_);
lean_ctor_set_uint64(v_reuseFailAlloc_1546_, sizeof(void*)*1, v_tid_1522_);
v___x_1538_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 4, v___x_1538_);
v___x_1540_ = v___x_1520_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_env_1510_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_nextMacroScope_1511_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_ngen_1512_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_auxDeclNGen_1513_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v_cache_1514_);
lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_recordedDeps_1515_);
lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_messages_1516_);
lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_infoState_1517_);
lean_ctor_set(v_reuseFailAlloc_1545_, 9, v_snapshotTasks_1518_);
v___x_1540_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_st_ref_put(v___y_1500_, v___x_1540_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1527_);
v___x_1543_ = v___x_1506_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1527_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1550_, lean_object* v_msg_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1550_, v_msg_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_box(0);
return v___x_1560_;
}
else
{
lean_object* v_key_1561_; lean_object* v_value_1562_; lean_object* v_tail_1563_; uint8_t v___x_1564_; 
v_key_1561_ = lean_ctor_get(v_x_1559_, 0);
v_value_1562_ = lean_ctor_get(v_x_1559_, 1);
v_tail_1563_ = lean_ctor_get(v_x_1559_, 2);
v___x_1564_ = lean_expr_eqv(v_key_1561_, v_a_1558_);
if (v___x_1564_ == 0)
{
v_x_1559_ = v_tail_1563_;
goto _start;
}
else
{
lean_object* v___x_1566_; 
lean_inc(v_value_1562_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_value_1562_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1567_, v_x_1568_);
lean_dec(v_x_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_buckets_1572_; lean_object* v___x_1573_; uint64_t v___x_1574_; uint64_t v___x_1575_; uint64_t v___x_1576_; uint64_t v_fold_1577_; uint64_t v___x_1578_; uint64_t v___x_1579_; uint64_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_buckets_1572_ = lean_ctor_get(v_m_1570_, 1);
v___x_1573_ = lean_array_get_size(v_buckets_1572_);
v___x_1574_ = l_Lean_Expr_hash(v_a_1571_);
v___x_1575_ = 32ULL;
v___x_1576_ = lean_uint64_shift_right(v___x_1574_, v___x_1575_);
v_fold_1577_ = lean_uint64_xor(v___x_1574_, v___x_1576_);
v___x_1578_ = 16ULL;
v___x_1579_ = lean_uint64_shift_right(v_fold_1577_, v___x_1578_);
v___x_1580_ = lean_uint64_xor(v_fold_1577_, v___x_1579_);
v___x_1581_ = lean_uint64_to_usize(v___x_1580_);
v___x_1582_ = lean_usize_of_nat(v___x_1573_);
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_sub(v___x_1582_, v___x_1583_);
v___x_1585_ = lean_usize_land(v___x_1581_, v___x_1584_);
v___x_1586_ = lean_array_uget_borrowed(v_buckets_1572_, v___x_1585_);
v___x_1587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1571_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1588_, v_a_1589_);
lean_dec_ref(v_a_1589_);
lean_dec_ref(v_m_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v_env_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1594_ = lean_st_ref_get(v___y_1592_);
v_env_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc_ref(v_env_1595_);
lean_dec(v___x_1594_);
v___x_1596_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1595_, v_declName_1591_);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1598_, v___y_1599_);
lean_dec(v___y_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(lean_object* v_name_1602_, lean_object* v_type_1603_, lean_object* v_val_1604_, lean_object* v_k_1605_, uint8_t v_nondep_1606_, uint8_t v_kind_1607_, uint8_t v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_box(v___y_1608_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1617_, 0, v_k_1605_);
lean_closure_set(v___f_1617_, 1, v___x_1616_);
lean_closure_set(v___f_1617_, 2, v___y_1609_);
lean_closure_set(v___f_1617_, 3, v___y_1610_);
v___x_1618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1602_, v_type_1603_, v_val_1604_, v___f_1617_, v_nondep_1606_, v_kind_1607_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1618_) == 0)
{
return v___x_1618_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg___boxed(lean_object* v_name_1627_, lean_object* v_type_1628_, lean_object* v_val_1629_, lean_object* v_k_1630_, lean_object* v_nondep_1631_, lean_object* v_kind_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_nondep_boxed_1641_; uint8_t v_kind_boxed_1642_; uint8_t v___y_62073__boxed_1643_; lean_object* v_res_1644_; 
v_nondep_boxed_1641_ = lean_unbox(v_nondep_1631_);
v_kind_boxed_1642_ = lean_unbox(v_kind_1632_);
v___y_62073__boxed_1643_ = lean_unbox(v___y_1633_);
v_res_1644_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_1627_, v_type_1628_, v_val_1629_, v_k_1630_, v_nondep_boxed_1641_, v_kind_boxed_1642_, v___y_62073__boxed_1643_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = l_Lean_instInhabitedExpr;
v___x_1647_ = lean_panic_fn_borrowed(v___x_1646_, v_msg_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1648_, lean_object* v_body_1649_, lean_object* v_x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v___y_62246__boxed_1659_; lean_object* v_res_1660_; 
v___y_62246__boxed_1659_ = lean_unbox(v___y_1651_);
v_res_1660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1648_, v_body_1649_, v_x_1650_, v___y_62246__boxed_1659_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1663_, lean_object* v_body_1664_, lean_object* v_x_1665_, uint8_t v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_array_push(v_fvars_1663_, v_x_1665_);
v___x_1675_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1674_, v_body_1664_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1676_, lean_object* v_body_1677_, lean_object* v_x_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
uint8_t v___y_62257__boxed_1687_; lean_object* v_res_1688_; 
v___y_62257__boxed_1687_ = lean_unbox(v___y_1679_);
v_res_1688_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1676_, v_body_1677_, v_x_1678_, v___y_62257__boxed_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1689_, lean_object* v_e_1690_, uint8_t v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
if (lean_obj_tag(v_e_1690_) == 6)
{
lean_object* v_binderName_1699_; lean_object* v_binderType_1700_; lean_object* v_body_1701_; uint8_t v_binderInfo_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_binderName_1699_ = lean_ctor_get(v_e_1690_, 0);
lean_inc(v_binderName_1699_);
v_binderType_1700_ = lean_ctor_get(v_e_1690_, 1);
lean_inc_ref(v_binderType_1700_);
v_body_1701_ = lean_ctor_get(v_e_1690_, 2);
lean_inc_ref(v_body_1701_);
v_binderInfo_1702_ = lean_ctor_get_uint8(v_e_1690_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1690_, 3);
lean_inc_ref(v_fvars_1689_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1703_, 0, v_fvars_1689_);
lean_closure_set(v___f_1703_, 1, v_body_1701_);
v___x_1704_ = lean_expr_instantiate_rev(v_binderType_1700_, v_fvars_1689_);
lean_dec_ref(v_fvars_1689_);
lean_dec_ref(v_binderType_1700_);
v___x_1705_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1704_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = 0;
v___x_1708_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_1699_, v_binderInfo_1702_, v_a_1706_, v___f_1703_, v___x_1707_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1708_;
}
else
{
lean_dec_ref(v___f_1703_);
lean_dec(v_binderName_1699_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_expr_instantiate_rev(v_e_1690_, v_fvars_1689_);
lean_dec_ref(v_e_1690_);
v___x_1710_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1709_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; uint8_t v___x_1712_; uint8_t v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = 0;
v___x_1713_ = 1;
v___x_1714_ = 1;
v___x_1715_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1689_, v_a_1711_, v___x_1712_, v___x_1713_, v___x_1712_, v___x_1713_, v___x_1714_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
lean_dec_ref(v_fvars_1689_);
return v___x_1715_;
}
else
{
lean_dec_ref(v_fvars_1689_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1716_, uint8_t v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
if (v_a_1717_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1726_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1725_, v_e_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1728_ = l_Lean_Meta_Sym_etaReduce(v_e_1716_);
lean_dec_ref(v_e_1716_);
v___x_1729_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1727_, v___x_1728_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1730_, lean_object* v_body_1731_, lean_object* v_x_1732_, uint8_t v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_array_push(v_fvars_1730_, v_x_1732_);
v___x_1742_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1741_, v_body_1731_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1743_, lean_object* v_body_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v___y_62268__boxed_1754_; lean_object* v_res_1755_; 
v___y_62268__boxed_1754_ = lean_unbox(v___y_1746_);
v_res_1755_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1743_, v_body_1744_, v_x_1745_, v___y_62268__boxed_1754_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1756_, lean_object* v_e_1757_, uint8_t v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
if (lean_obj_tag(v_e_1757_) == 8)
{
lean_object* v_declName_1766_; lean_object* v_type_1767_; lean_object* v_value_1768_; lean_object* v_body_1769_; uint8_t v_nondep_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_declName_1766_ = lean_ctor_get(v_e_1757_, 0);
lean_inc(v_declName_1766_);
v_type_1767_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_type_1767_);
v_value_1768_ = lean_ctor_get(v_e_1757_, 2);
lean_inc_ref(v_value_1768_);
v_body_1769_ = lean_ctor_get(v_e_1757_, 3);
lean_inc_ref(v_body_1769_);
v_nondep_1770_ = lean_ctor_get_uint8(v_e_1757_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1757_, 4);
lean_inc_ref(v_fvars_1756_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1771_, 0, v_fvars_1756_);
lean_closure_set(v___f_1771_, 1, v_body_1769_);
v___x_1772_ = lean_expr_instantiate_rev(v_type_1767_, v_fvars_1756_);
lean_dec_ref(v_type_1767_);
v___x_1773_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1772_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = lean_expr_instantiate_rev(v_value_1768_, v_fvars_1756_);
lean_dec_ref(v_fvars_1756_);
lean_dec_ref(v_value_1768_);
v___x_1776_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1775_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = 0;
v___x_1779_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_declName_1766_, v_a_1774_, v_a_1777_, v___f_1771_, v_nondep_1770_, v___x_1778_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1779_;
}
else
{
lean_dec(v_a_1774_);
lean_dec_ref(v___f_1771_);
lean_dec(v_declName_1766_);
return v___x_1776_;
}
}
else
{
lean_dec_ref(v___f_1771_);
lean_dec_ref(v_value_1768_);
lean_dec(v_declName_1766_);
lean_dec_ref(v_fvars_1756_);
return v___x_1773_;
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_expr_instantiate_rev(v_e_1757_, v_fvars_1756_);
lean_dec_ref(v_e_1757_);
v___x_1781_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1780_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; uint8_t v___x_1783_; uint8_t v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = 1;
v___x_1784_ = 0;
v___x_1785_ = 1;
v___x_1786_ = l_Lean_Meta_mkLetFVars(v_fvars_1756_, v_a_1782_, v___x_1783_, v___x_1784_, v___x_1785_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec_ref(v_fvars_1756_);
return v___x_1786_;
}
else
{
lean_dec_ref(v_fvars_1756_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1787_, uint8_t v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
if (v_a_1788_ == 0)
{
uint8_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = 1;
v___x_1797_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1787_, v___x_1796_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1799_, uint8_t v_report_1800_, uint8_t v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; 
lean_inc(v_a_1807_);
lean_inc_ref(v_a_1806_);
lean_inc(v_a_1805_);
lean_inc_ref(v_a_1804_);
lean_inc_ref(v_e_1799_);
v___x_1809_ = lean_infer_type(v_e_1799_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc_n(v_a_1810_, 2);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = l_Lean_Meta_isProp(v_a_1810_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1824_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
if (v_a_1801_ == 0)
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_unbox(v_a_1812_);
lean_dec(v_a_1812_);
if (v___x_1820_ == 0)
{
lean_del_object(v___x_1814_);
goto v___jp_1816_;
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_a_1810_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_e_1799_);
v___x_1822_ = v___x_1814_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_e_1799_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_del_object(v___x_1814_);
lean_dec(v_a_1812_);
goto v___jp_1816_;
}
v___jp_1816_:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1810_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1819_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1799_, v_a_1818_, v_report_1800_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
return v___x_1819_;
}
else
{
lean_dec_ref(v_e_1799_);
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_a_1810_);
lean_dec_ref(v_e_1799_);
v_a_1825_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1811_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1811_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_dec_ref(v_e_1799_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1833_, uint8_t v_report_1834_, uint8_t v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
if (v_a_1835_ == 0)
{
lean_object* v___x_1843_; lean_object* v_canon_1844_; lean_object* v_cache_1845_; lean_object* v___x_1846_; 
v___x_1843_ = lean_st_ref_get(v_a_1837_);
v_canon_1844_ = lean_ctor_get(v___x_1843_, 10);
lean_inc_ref(v_canon_1844_);
lean_dec(v___x_1843_);
v_cache_1845_ = lean_ctor_get(v_canon_1844_, 0);
lean_inc_ref(v_cache_1845_);
lean_dec_ref(v_canon_1844_);
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1845_, v_e_1833_);
lean_dec_ref(v_cache_1845_);
if (lean_obj_tag(v___x_1846_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_e_1833_);
v_val_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_val_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_object* v___x_1855_; 
lean_dec(v___x_1846_);
lean_inc_ref(v_e_1833_);
v___x_1855_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1833_, v_report_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1895_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1895_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1895_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v_canon_1861_; lean_object* v_share_1862_; lean_object* v_maxFVar_1863_; lean_object* v_proofInstInfo_1864_; lean_object* v_proofInstInfoFVar_1865_; lean_object* v_inferType_1866_; lean_object* v_getLevel_1867_; lean_object* v_congrInfo_1868_; lean_object* v_defEqI_1869_; lean_object* v_extensions_1870_; lean_object* v_issues_1871_; lean_object* v_instanceOverrides_1872_; uint8_t v_debug_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1894_; 
v___x_1860_ = lean_st_ref_take(v_a_1837_);
v_canon_1861_ = lean_ctor_get(v___x_1860_, 10);
v_share_1862_ = lean_ctor_get(v___x_1860_, 0);
v_maxFVar_1863_ = lean_ctor_get(v___x_1860_, 1);
v_proofInstInfo_1864_ = lean_ctor_get(v___x_1860_, 2);
v_proofInstInfoFVar_1865_ = lean_ctor_get(v___x_1860_, 3);
v_inferType_1866_ = lean_ctor_get(v___x_1860_, 4);
v_getLevel_1867_ = lean_ctor_get(v___x_1860_, 5);
v_congrInfo_1868_ = lean_ctor_get(v___x_1860_, 6);
v_defEqI_1869_ = lean_ctor_get(v___x_1860_, 7);
v_extensions_1870_ = lean_ctor_get(v___x_1860_, 8);
v_issues_1871_ = lean_ctor_get(v___x_1860_, 9);
v_instanceOverrides_1872_ = lean_ctor_get(v___x_1860_, 11);
v_debug_1873_ = lean_ctor_get_uint8(v___x_1860_, sizeof(void*)*12);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1875_ = v___x_1860_;
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_instanceOverrides_1872_);
lean_inc(v_canon_1861_);
lean_inc(v_issues_1871_);
lean_inc(v_extensions_1870_);
lean_inc(v_defEqI_1869_);
lean_inc(v_congrInfo_1868_);
lean_inc(v_getLevel_1867_);
lean_inc(v_inferType_1866_);
lean_inc(v_proofInstInfoFVar_1865_);
lean_inc(v_proofInstInfo_1864_);
lean_inc(v_maxFVar_1863_);
lean_inc(v_share_1862_);
lean_dec(v___x_1860_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_cache_1877_; lean_object* v_cacheInType_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1893_; 
v_cache_1877_ = lean_ctor_get(v_canon_1861_, 0);
v_cacheInType_1878_ = lean_ctor_get(v_canon_1861_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_canon_1861_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1880_ = v_canon_1861_;
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_cacheInType_1878_);
lean_inc(v_cache_1877_);
lean_dec(v_canon_1861_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_inc(v_a_1856_);
v___x_1882_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1877_, v_e_1833_, v_a_1856_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_cacheInType_1878_);
v___x_1884_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 10, v___x_1884_);
v___x_1886_ = v___x_1875_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_share_1862_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_maxFVar_1863_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_proofInstInfo_1864_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_proofInstInfoFVar_1865_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_inferType_1866_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_getLevel_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_congrInfo_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_defEqI_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_extensions_1870_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_issues_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 10, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1891_, 11, v_instanceOverrides_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*12, v_debug_1873_);
v___x_1886_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_st_ref_put(v_a_1837_, v___x_1886_);
if (v_isShared_1859_ == 0)
{
v___x_1889_ = v___x_1858_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1856_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1833_);
return v___x_1855_;
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v_canon_1897_; lean_object* v_cacheInType_1898_; lean_object* v___x_1899_; 
v___x_1896_ = lean_st_ref_get(v_a_1837_);
v_canon_1897_ = lean_ctor_get(v___x_1896_, 10);
lean_inc_ref(v_canon_1897_);
lean_dec(v___x_1896_);
v_cacheInType_1898_ = lean_ctor_get(v_canon_1897_, 1);
lean_inc_ref(v_cacheInType_1898_);
lean_dec_ref(v_canon_1897_);
v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1898_, v_e_1833_);
lean_dec_ref(v_cacheInType_1898_);
if (lean_obj_tag(v___x_1899_) == 1)
{
lean_object* v_val_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v_e_1833_);
v_val_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_val_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 0);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_val_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v___x_1908_; 
lean_dec(v___x_1899_);
lean_inc_ref(v_e_1833_);
v___x_1908_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1833_, v_report_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1948_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1948_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1948_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v_canon_1914_; lean_object* v_share_1915_; lean_object* v_maxFVar_1916_; lean_object* v_proofInstInfo_1917_; lean_object* v_proofInstInfoFVar_1918_; lean_object* v_inferType_1919_; lean_object* v_getLevel_1920_; lean_object* v_congrInfo_1921_; lean_object* v_defEqI_1922_; lean_object* v_extensions_1923_; lean_object* v_issues_1924_; lean_object* v_instanceOverrides_1925_; uint8_t v_debug_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1947_; 
v___x_1913_ = lean_st_ref_take(v_a_1837_);
v_canon_1914_ = lean_ctor_get(v___x_1913_, 10);
v_share_1915_ = lean_ctor_get(v___x_1913_, 0);
v_maxFVar_1916_ = lean_ctor_get(v___x_1913_, 1);
v_proofInstInfo_1917_ = lean_ctor_get(v___x_1913_, 2);
v_proofInstInfoFVar_1918_ = lean_ctor_get(v___x_1913_, 3);
v_inferType_1919_ = lean_ctor_get(v___x_1913_, 4);
v_getLevel_1920_ = lean_ctor_get(v___x_1913_, 5);
v_congrInfo_1921_ = lean_ctor_get(v___x_1913_, 6);
v_defEqI_1922_ = lean_ctor_get(v___x_1913_, 7);
v_extensions_1923_ = lean_ctor_get(v___x_1913_, 8);
v_issues_1924_ = lean_ctor_get(v___x_1913_, 9);
v_instanceOverrides_1925_ = lean_ctor_get(v___x_1913_, 11);
v_debug_1926_ = lean_ctor_get_uint8(v___x_1913_, sizeof(void*)*12);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1928_ = v___x_1913_;
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_instanceOverrides_1925_);
lean_inc(v_canon_1914_);
lean_inc(v_issues_1924_);
lean_inc(v_extensions_1923_);
lean_inc(v_defEqI_1922_);
lean_inc(v_congrInfo_1921_);
lean_inc(v_getLevel_1920_);
lean_inc(v_inferType_1919_);
lean_inc(v_proofInstInfoFVar_1918_);
lean_inc(v_proofInstInfo_1917_);
lean_inc(v_maxFVar_1916_);
lean_inc(v_share_1915_);
lean_dec(v___x_1913_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_cache_1930_; lean_object* v_cacheInType_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1946_; 
v_cache_1930_ = lean_ctor_get(v_canon_1914_, 0);
v_cacheInType_1931_ = lean_ctor_get(v_canon_1914_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_canon_1914_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1933_ = v_canon_1914_;
v_isShared_1934_ = v_isSharedCheck_1946_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_cacheInType_1931_);
lean_inc(v_cache_1930_);
lean_dec(v_canon_1914_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1946_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_inc(v_a_1909_);
v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1931_, v_e_1833_, v_a_1909_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_cache_1930_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 10, v___x_1937_);
v___x_1939_ = v___x_1928_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_share_1915_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_maxFVar_1916_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_proofInstInfo_1917_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_proofInstInfoFVar_1918_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_inferType_1919_);
lean_ctor_set(v_reuseFailAlloc_1944_, 5, v_getLevel_1920_);
lean_ctor_set(v_reuseFailAlloc_1944_, 6, v_congrInfo_1921_);
lean_ctor_set(v_reuseFailAlloc_1944_, 7, v_defEqI_1922_);
lean_ctor_set(v_reuseFailAlloc_1944_, 8, v_extensions_1923_);
lean_ctor_set(v_reuseFailAlloc_1944_, 9, v_issues_1924_);
lean_ctor_set(v_reuseFailAlloc_1944_, 10, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1944_, 11, v_instanceOverrides_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*12, v_debug_1926_);
v___x_1939_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_st_ref_put(v_a_1837_, v___x_1939_);
if (v_isShared_1912_ == 0)
{
v___x_1942_ = v___x_1911_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1909_);
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
}
}
else
{
lean_dec_ref(v_e_1833_);
return v___x_1908_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1965_ = l_Lean_mkConst(v___x_1964_, v___x_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1966_, lean_object* v_prop_1967_, lean_object* v_inst_1968_, lean_object* v_e_1969_, uint8_t v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; 
lean_inc_ref(v_prop_1967_);
v___x_1978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1967_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2021_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2021_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2021_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___y_1984_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1979_);
v___x_1990_ = l_Lean_Expr_app___override(v___x_1989_, v_a_1979_);
if (v_a_1970_ == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1990_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___y_1994_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
if (lean_obj_tag(v_a_1992_) == 0)
{
lean_inc_ref(v_inst_1968_);
v___y_1994_ = v_inst_1968_;
goto v___jp_1993_;
}
else
{
lean_object* v_val_2010_; 
v_val_2010_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v_a_1992_, 1);
v___y_1994_ = v_val_2010_;
goto v___jp_1993_;
}
v___jp_1993_:
{
lean_object* v___x_1995_; 
lean_inc_ref(v_inst_1968_);
v___x_1995_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1968_, v___y_1994_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2009_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2009_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2009_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
size_t v___x_2000_; size_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = lean_ptr_addr(v_prop_1967_);
lean_dec_ref(v_prop_1967_);
v___x_2001_ = lean_ptr_addr(v_a_1979_);
v___x_2002_ = lean_usize_dec_eq(v___x_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_del_object(v___x_1998_);
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_inst_1968_);
v___y_1984_ = v_a_1996_;
goto v___jp_1983_;
}
else
{
size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = lean_ptr_addr(v_inst_1968_);
lean_dec_ref(v_inst_1968_);
v___x_2004_ = lean_ptr_addr(v_a_1996_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_del_object(v___x_1998_);
lean_dec_ref(v_e_1969_);
v___y_1984_ = v_a_1996_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_a_1996_);
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec_ref(v_g_1966_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_e_1969_);
v___x_2007_ = v___x_1998_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_e_1969_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_inst_1968_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_inst_1968_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
v_a_2011_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1991_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1991_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
uint8_t v___x_2019_; lean_object* v___x_2020_; 
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
v___x_2019_ = 0;
v___x_2020_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1968_, v___x_1990_, v___x_2019_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
return v___x_2020_;
}
v___jp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = l_Lean_mkAppB(v_g_1966_, v_a_1979_, v___y_1984_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1985_);
v___x_1987_ = v___x_1981_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_dec_ref(v_e_1969_);
lean_dec_ref(v_inst_1968_);
lean_dec_ref(v_prop_1967_);
lean_dec_ref(v_g_1966_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2022_, lean_object* v_prop_2023_, lean_object* v_h_2024_, lean_object* v_e_2025_, uint8_t v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
if (v_a_2026_ == 0)
{
lean_object* v___x_2034_; lean_object* v_canon_2035_; lean_object* v_cache_2036_; lean_object* v___x_2037_; 
v___x_2034_ = lean_st_ref_get(v_a_2028_);
v_canon_2035_ = lean_ctor_get(v___x_2034_, 10);
lean_inc_ref(v_canon_2035_);
lean_dec(v___x_2034_);
v_cache_2036_ = lean_ctor_get(v_canon_2035_, 0);
lean_inc_ref(v_cache_2036_);
lean_dec_ref(v_canon_2035_);
v___x_2037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2036_, v_e_2025_);
lean_dec_ref(v_cache_2036_);
if (lean_obj_tag(v___x_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_e_2025_);
lean_dec_ref(v_h_2024_);
lean_dec_ref(v_prop_2023_);
lean_dec_ref(v_g_2022_);
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_val_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_val_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v___x_2046_; 
lean_dec(v___x_2037_);
lean_inc_ref(v_e_2025_);
v___x_2046_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2022_, v_prop_2023_, v_h_2024_, v_e_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2086_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2086_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2086_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v_canon_2052_; lean_object* v_share_2053_; lean_object* v_maxFVar_2054_; lean_object* v_proofInstInfo_2055_; lean_object* v_proofInstInfoFVar_2056_; lean_object* v_inferType_2057_; lean_object* v_getLevel_2058_; lean_object* v_congrInfo_2059_; lean_object* v_defEqI_2060_; lean_object* v_extensions_2061_; lean_object* v_issues_2062_; lean_object* v_instanceOverrides_2063_; uint8_t v_debug_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2085_; 
v___x_2051_ = lean_st_ref_take(v_a_2028_);
v_canon_2052_ = lean_ctor_get(v___x_2051_, 10);
v_share_2053_ = lean_ctor_get(v___x_2051_, 0);
v_maxFVar_2054_ = lean_ctor_get(v___x_2051_, 1);
v_proofInstInfo_2055_ = lean_ctor_get(v___x_2051_, 2);
v_proofInstInfoFVar_2056_ = lean_ctor_get(v___x_2051_, 3);
v_inferType_2057_ = lean_ctor_get(v___x_2051_, 4);
v_getLevel_2058_ = lean_ctor_get(v___x_2051_, 5);
v_congrInfo_2059_ = lean_ctor_get(v___x_2051_, 6);
v_defEqI_2060_ = lean_ctor_get(v___x_2051_, 7);
v_extensions_2061_ = lean_ctor_get(v___x_2051_, 8);
v_issues_2062_ = lean_ctor_get(v___x_2051_, 9);
v_instanceOverrides_2063_ = lean_ctor_get(v___x_2051_, 11);
v_debug_2064_ = lean_ctor_get_uint8(v___x_2051_, sizeof(void*)*12);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2066_ = v___x_2051_;
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_instanceOverrides_2063_);
lean_inc(v_canon_2052_);
lean_inc(v_issues_2062_);
lean_inc(v_extensions_2061_);
lean_inc(v_defEqI_2060_);
lean_inc(v_congrInfo_2059_);
lean_inc(v_getLevel_2058_);
lean_inc(v_inferType_2057_);
lean_inc(v_proofInstInfoFVar_2056_);
lean_inc(v_proofInstInfo_2055_);
lean_inc(v_maxFVar_2054_);
lean_inc(v_share_2053_);
lean_dec(v___x_2051_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_cache_2068_; lean_object* v_cacheInType_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2084_; 
v_cache_2068_ = lean_ctor_get(v_canon_2052_, 0);
v_cacheInType_2069_ = lean_ctor_get(v_canon_2052_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_canon_2052_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2071_ = v_canon_2052_;
v_isShared_2072_ = v_isSharedCheck_2084_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_cacheInType_2069_);
lean_inc(v_cache_2068_);
lean_dec(v_canon_2052_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2084_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_inc(v_a_2047_);
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2068_, v_e_2025_, v_a_2047_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_cacheInType_2069_);
v___x_2075_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 10, v___x_2075_);
v___x_2077_ = v___x_2066_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_share_2053_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_maxFVar_2054_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_proofInstInfo_2055_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_proofInstInfoFVar_2056_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_inferType_2057_);
lean_ctor_set(v_reuseFailAlloc_2082_, 5, v_getLevel_2058_);
lean_ctor_set(v_reuseFailAlloc_2082_, 6, v_congrInfo_2059_);
lean_ctor_set(v_reuseFailAlloc_2082_, 7, v_defEqI_2060_);
lean_ctor_set(v_reuseFailAlloc_2082_, 8, v_extensions_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 9, v_issues_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 10, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 11, v_instanceOverrides_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2082_, sizeof(void*)*12, v_debug_2064_);
v___x_2077_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_st_ref_put(v_a_2028_, v___x_2077_);
if (v_isShared_2050_ == 0)
{
v___x_2080_ = v___x_2049_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2047_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2025_);
return v___x_2046_;
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v_canon_2088_; lean_object* v_cacheInType_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_st_ref_get(v_a_2028_);
v_canon_2088_ = lean_ctor_get(v___x_2087_, 10);
lean_inc_ref(v_canon_2088_);
lean_dec(v___x_2087_);
v_cacheInType_2089_ = lean_ctor_get(v_canon_2088_, 1);
lean_inc_ref(v_cacheInType_2089_);
lean_dec_ref(v_canon_2088_);
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2089_, v_e_2025_);
lean_dec_ref(v_cacheInType_2089_);
if (lean_obj_tag(v___x_2090_) == 1)
{
lean_object* v_val_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_e_2025_);
lean_dec_ref(v_h_2024_);
lean_dec_ref(v_prop_2023_);
lean_dec_ref(v_g_2022_);
v_val_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_val_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 0);
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2099_; 
lean_dec(v___x_2090_);
lean_inc_ref(v_e_2025_);
v___x_2099_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2022_, v_prop_2023_, v_h_2024_, v_e_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2139_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2139_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2139_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v_canon_2105_; lean_object* v_share_2106_; lean_object* v_maxFVar_2107_; lean_object* v_proofInstInfo_2108_; lean_object* v_proofInstInfoFVar_2109_; lean_object* v_inferType_2110_; lean_object* v_getLevel_2111_; lean_object* v_congrInfo_2112_; lean_object* v_defEqI_2113_; lean_object* v_extensions_2114_; lean_object* v_issues_2115_; lean_object* v_instanceOverrides_2116_; uint8_t v_debug_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2138_; 
v___x_2104_ = lean_st_ref_take(v_a_2028_);
v_canon_2105_ = lean_ctor_get(v___x_2104_, 10);
v_share_2106_ = lean_ctor_get(v___x_2104_, 0);
v_maxFVar_2107_ = lean_ctor_get(v___x_2104_, 1);
v_proofInstInfo_2108_ = lean_ctor_get(v___x_2104_, 2);
v_proofInstInfoFVar_2109_ = lean_ctor_get(v___x_2104_, 3);
v_inferType_2110_ = lean_ctor_get(v___x_2104_, 4);
v_getLevel_2111_ = lean_ctor_get(v___x_2104_, 5);
v_congrInfo_2112_ = lean_ctor_get(v___x_2104_, 6);
v_defEqI_2113_ = lean_ctor_get(v___x_2104_, 7);
v_extensions_2114_ = lean_ctor_get(v___x_2104_, 8);
v_issues_2115_ = lean_ctor_get(v___x_2104_, 9);
v_instanceOverrides_2116_ = lean_ctor_get(v___x_2104_, 11);
v_debug_2117_ = lean_ctor_get_uint8(v___x_2104_, sizeof(void*)*12);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2119_ = v___x_2104_;
v_isShared_2120_ = v_isSharedCheck_2138_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_instanceOverrides_2116_);
lean_inc(v_canon_2105_);
lean_inc(v_issues_2115_);
lean_inc(v_extensions_2114_);
lean_inc(v_defEqI_2113_);
lean_inc(v_congrInfo_2112_);
lean_inc(v_getLevel_2111_);
lean_inc(v_inferType_2110_);
lean_inc(v_proofInstInfoFVar_2109_);
lean_inc(v_proofInstInfo_2108_);
lean_inc(v_maxFVar_2107_);
lean_inc(v_share_2106_);
lean_dec(v___x_2104_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2138_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_cache_2121_; lean_object* v_cacheInType_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2137_; 
v_cache_2121_ = lean_ctor_get(v_canon_2105_, 0);
v_cacheInType_2122_ = lean_ctor_get(v_canon_2105_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_canon_2105_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2124_ = v_canon_2105_;
v_isShared_2125_ = v_isSharedCheck_2137_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_cacheInType_2122_);
lean_inc(v_cache_2121_);
lean_dec(v_canon_2105_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2137_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_inc(v_a_2100_);
v___x_2126_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2122_, v_e_2025_, v_a_2100_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_cache_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 10, v___x_2128_);
v___x_2130_ = v___x_2119_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_share_2106_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_maxFVar_2107_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_proofInstInfo_2108_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_proofInstInfoFVar_2109_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_inferType_2110_);
lean_ctor_set(v_reuseFailAlloc_2135_, 5, v_getLevel_2111_);
lean_ctor_set(v_reuseFailAlloc_2135_, 6, v_congrInfo_2112_);
lean_ctor_set(v_reuseFailAlloc_2135_, 7, v_defEqI_2113_);
lean_ctor_set(v_reuseFailAlloc_2135_, 8, v_extensions_2114_);
lean_ctor_set(v_reuseFailAlloc_2135_, 9, v_issues_2115_);
lean_ctor_set(v_reuseFailAlloc_2135_, 10, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2135_, 11, v_instanceOverrides_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2135_, sizeof(void*)*12, v_debug_2117_);
v___x_2130_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_st_ref_put(v_a_2028_, v___x_2130_);
if (v_isShared_2103_ == 0)
{
v___x_2133_ = v___x_2102_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2100_);
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
}
}
else
{
lean_dec_ref(v_e_2025_);
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2140_, lean_object* v_prop_2141_, lean_object* v_h_2142_, lean_object* v_e_2143_, uint8_t v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_a_2153_; lean_object* v___y_2188_; 
if (v_a_2144_ == 0)
{
lean_object* v___x_2229_; lean_object* v_canon_2230_; lean_object* v_cache_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_st_ref_get(v_a_2146_);
v_canon_2230_ = lean_ctor_get(v___x_2229_, 10);
lean_inc_ref(v_canon_2230_);
lean_dec(v___x_2229_);
v_cache_2231_ = lean_ctor_get(v_canon_2230_, 0);
lean_inc_ref(v_cache_2231_);
lean_dec_ref(v_canon_2230_);
v___x_2232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2231_, v_e_2143_);
lean_dec_ref(v_cache_2231_);
if (lean_obj_tag(v___x_2232_) == 1)
{
lean_object* v_val_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_e_2143_);
lean_dec_ref(v_h_2142_);
lean_dec_ref(v_prop_2141_);
lean_dec_ref(v_g_2140_);
v_val_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_val_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set_tag(v___x_2235_, 0);
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_val_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_object* v___x_2241_; 
lean_dec(v___x_2232_);
lean_inc_ref(v_prop_2141_);
v___x_2241_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2141_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc_n(v_a_2242_, 2);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2243_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2242_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___y_2246_; lean_object* v___y_2249_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
if (lean_obj_tag(v_a_2244_) == 0)
{
lean_inc_ref(v_h_2142_);
v___y_2249_ = v_h_2142_;
goto v___jp_2248_;
}
else
{
lean_object* v_val_2256_; 
v_val_2256_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v_a_2244_, 1);
v___y_2249_ = v_val_2256_;
goto v___jp_2248_;
}
v___jp_2245_:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_mkAppB(v_g_2140_, v_a_2242_, v___y_2246_);
v_a_2153_ = v___x_2247_;
goto v___jp_2152_;
}
v___jp_2248_:
{
size_t v___x_2250_; size_t v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = lean_ptr_addr(v_prop_2141_);
lean_dec_ref(v_prop_2141_);
v___x_2251_ = lean_ptr_addr(v_a_2242_);
v___x_2252_ = lean_usize_dec_eq(v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec_ref(v_h_2142_);
v___y_2246_ = v___y_2249_;
goto v___jp_2245_;
}
else
{
size_t v___x_2253_; size_t v___x_2254_; uint8_t v___x_2255_; 
v___x_2253_ = lean_ptr_addr(v_h_2142_);
lean_dec_ref(v_h_2142_);
v___x_2254_ = lean_ptr_addr(v___y_2249_);
v___x_2255_ = lean_usize_dec_eq(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
v___y_2246_ = v___y_2249_;
goto v___jp_2245_;
}
else
{
lean_dec_ref(v___y_2249_);
lean_dec(v_a_2242_);
lean_dec_ref(v_g_2140_);
lean_inc_ref(v_e_2143_);
v_a_2153_ = v_e_2143_;
goto v___jp_2152_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_a_2242_);
lean_dec_ref(v_e_2143_);
lean_dec_ref(v_h_2142_);
lean_dec_ref(v_prop_2141_);
lean_dec_ref(v_g_2140_);
v_a_2257_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2243_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2243_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
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
else
{
lean_dec_ref(v_h_2142_);
lean_dec_ref(v_prop_2141_);
lean_dec_ref(v_g_2140_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2241_, 1);
v_a_2153_ = v_a_2265_;
goto v___jp_2152_;
}
else
{
lean_dec_ref(v_e_2143_);
return v___x_2241_;
}
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v_canon_2267_; lean_object* v_cacheInType_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v_g_2140_);
v___x_2266_ = lean_st_ref_get(v_a_2146_);
v_canon_2267_ = lean_ctor_get(v___x_2266_, 10);
lean_inc_ref(v_canon_2267_);
lean_dec(v___x_2266_);
v_cacheInType_2268_ = lean_ctor_get(v_canon_2267_, 1);
lean_inc_ref(v_cacheInType_2268_);
lean_dec_ref(v_canon_2267_);
v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2268_, v_e_2143_);
lean_dec_ref(v_cacheInType_2268_);
if (lean_obj_tag(v___x_2269_) == 1)
{
lean_object* v_val_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_e_2143_);
lean_dec_ref(v_h_2142_);
lean_dec_ref(v_prop_2141_);
v_val_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_val_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 0);
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_val_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
lean_object* v___x_2278_; 
lean_dec(v___x_2269_);
v___x_2278_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2141_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = 0;
v___x_2281_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_2142_, v_a_2279_, v___x_2280_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
v___y_2188_ = v___x_2281_;
goto v___jp_2187_;
}
else
{
lean_dec_ref(v_h_2142_);
v___y_2188_ = v___x_2278_;
goto v___jp_2187_;
}
}
}
v___jp_2152_:
{
lean_object* v___x_2154_; lean_object* v_canon_2155_; lean_object* v_share_2156_; lean_object* v_maxFVar_2157_; lean_object* v_proofInstInfo_2158_; lean_object* v_proofInstInfoFVar_2159_; lean_object* v_inferType_2160_; lean_object* v_getLevel_2161_; lean_object* v_congrInfo_2162_; lean_object* v_defEqI_2163_; lean_object* v_extensions_2164_; lean_object* v_issues_2165_; lean_object* v_instanceOverrides_2166_; uint8_t v_debug_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2186_; 
v___x_2154_ = lean_st_ref_take(v_a_2146_);
v_canon_2155_ = lean_ctor_get(v___x_2154_, 10);
v_share_2156_ = lean_ctor_get(v___x_2154_, 0);
v_maxFVar_2157_ = lean_ctor_get(v___x_2154_, 1);
v_proofInstInfo_2158_ = lean_ctor_get(v___x_2154_, 2);
v_proofInstInfoFVar_2159_ = lean_ctor_get(v___x_2154_, 3);
v_inferType_2160_ = lean_ctor_get(v___x_2154_, 4);
v_getLevel_2161_ = lean_ctor_get(v___x_2154_, 5);
v_congrInfo_2162_ = lean_ctor_get(v___x_2154_, 6);
v_defEqI_2163_ = lean_ctor_get(v___x_2154_, 7);
v_extensions_2164_ = lean_ctor_get(v___x_2154_, 8);
v_issues_2165_ = lean_ctor_get(v___x_2154_, 9);
v_instanceOverrides_2166_ = lean_ctor_get(v___x_2154_, 11);
v_debug_2167_ = lean_ctor_get_uint8(v___x_2154_, sizeof(void*)*12);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2169_ = v___x_2154_;
v_isShared_2170_ = v_isSharedCheck_2186_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_instanceOverrides_2166_);
lean_inc(v_canon_2155_);
lean_inc(v_issues_2165_);
lean_inc(v_extensions_2164_);
lean_inc(v_defEqI_2163_);
lean_inc(v_congrInfo_2162_);
lean_inc(v_getLevel_2161_);
lean_inc(v_inferType_2160_);
lean_inc(v_proofInstInfoFVar_2159_);
lean_inc(v_proofInstInfo_2158_);
lean_inc(v_maxFVar_2157_);
lean_inc(v_share_2156_);
lean_dec(v___x_2154_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2186_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_cache_2171_; lean_object* v_cacheInType_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2185_; 
v_cache_2171_ = lean_ctor_get(v_canon_2155_, 0);
v_cacheInType_2172_ = lean_ctor_get(v_canon_2155_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_canon_2155_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2174_ = v_canon_2155_;
v_isShared_2175_ = v_isSharedCheck_2185_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_cacheInType_2172_);
lean_inc(v_cache_2171_);
lean_dec(v_canon_2155_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2185_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_inc_ref(v_a_2153_);
v___x_2176_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2171_, v_e_2143_, v_a_2153_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_cacheInType_2172_);
v___x_2178_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 10, v___x_2178_);
v___x_2180_ = v___x_2169_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_share_2156_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_maxFVar_2157_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_proofInstInfo_2158_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_proofInstInfoFVar_2159_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_inferType_2160_);
lean_ctor_set(v_reuseFailAlloc_2183_, 5, v_getLevel_2161_);
lean_ctor_set(v_reuseFailAlloc_2183_, 6, v_congrInfo_2162_);
lean_ctor_set(v_reuseFailAlloc_2183_, 7, v_defEqI_2163_);
lean_ctor_set(v_reuseFailAlloc_2183_, 8, v_extensions_2164_);
lean_ctor_set(v_reuseFailAlloc_2183_, 9, v_issues_2165_);
lean_ctor_set(v_reuseFailAlloc_2183_, 10, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2183_, 11, v_instanceOverrides_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*12, v_debug_2167_);
v___x_2180_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_st_ref_put(v_a_2146_, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2153_);
return v___x_2182_;
}
}
}
}
}
v___jp_2187_:
{
if (lean_obj_tag(v___y_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2228_; 
v_a_2189_ = lean_ctor_get(v___y_2188_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___y_2188_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2191_ = v___y_2188_;
v_isShared_2192_ = v_isSharedCheck_2228_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___y_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2228_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v_canon_2194_; lean_object* v_share_2195_; lean_object* v_maxFVar_2196_; lean_object* v_proofInstInfo_2197_; lean_object* v_proofInstInfoFVar_2198_; lean_object* v_inferType_2199_; lean_object* v_getLevel_2200_; lean_object* v_congrInfo_2201_; lean_object* v_defEqI_2202_; lean_object* v_extensions_2203_; lean_object* v_issues_2204_; lean_object* v_instanceOverrides_2205_; uint8_t v_debug_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2227_; 
v___x_2193_ = lean_st_ref_take(v_a_2146_);
v_canon_2194_ = lean_ctor_get(v___x_2193_, 10);
v_share_2195_ = lean_ctor_get(v___x_2193_, 0);
v_maxFVar_2196_ = lean_ctor_get(v___x_2193_, 1);
v_proofInstInfo_2197_ = lean_ctor_get(v___x_2193_, 2);
v_proofInstInfoFVar_2198_ = lean_ctor_get(v___x_2193_, 3);
v_inferType_2199_ = lean_ctor_get(v___x_2193_, 4);
v_getLevel_2200_ = lean_ctor_get(v___x_2193_, 5);
v_congrInfo_2201_ = lean_ctor_get(v___x_2193_, 6);
v_defEqI_2202_ = lean_ctor_get(v___x_2193_, 7);
v_extensions_2203_ = lean_ctor_get(v___x_2193_, 8);
v_issues_2204_ = lean_ctor_get(v___x_2193_, 9);
v_instanceOverrides_2205_ = lean_ctor_get(v___x_2193_, 11);
v_debug_2206_ = lean_ctor_get_uint8(v___x_2193_, sizeof(void*)*12);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2208_ = v___x_2193_;
v_isShared_2209_ = v_isSharedCheck_2227_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_instanceOverrides_2205_);
lean_inc(v_canon_2194_);
lean_inc(v_issues_2204_);
lean_inc(v_extensions_2203_);
lean_inc(v_defEqI_2202_);
lean_inc(v_congrInfo_2201_);
lean_inc(v_getLevel_2200_);
lean_inc(v_inferType_2199_);
lean_inc(v_proofInstInfoFVar_2198_);
lean_inc(v_proofInstInfo_2197_);
lean_inc(v_maxFVar_2196_);
lean_inc(v_share_2195_);
lean_dec(v___x_2193_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2227_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_cache_2210_; lean_object* v_cacheInType_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2226_; 
v_cache_2210_ = lean_ctor_get(v_canon_2194_, 0);
v_cacheInType_2211_ = lean_ctor_get(v_canon_2194_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_canon_2194_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2213_ = v_canon_2194_;
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_cacheInType_2211_);
lean_inc(v_cache_2210_);
lean_dec(v_canon_2194_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_inc(v_a_2189_);
v___x_2215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2211_, v_e_2143_, v_a_2189_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2215_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_cache_2210_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 10, v___x_2217_);
v___x_2219_ = v___x_2208_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_share_2195_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_maxFVar_2196_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_proofInstInfo_2197_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_proofInstInfoFVar_2198_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_inferType_2199_);
lean_ctor_set(v_reuseFailAlloc_2224_, 5, v_getLevel_2200_);
lean_ctor_set(v_reuseFailAlloc_2224_, 6, v_congrInfo_2201_);
lean_ctor_set(v_reuseFailAlloc_2224_, 7, v_defEqI_2202_);
lean_ctor_set(v_reuseFailAlloc_2224_, 8, v_extensions_2203_);
lean_ctor_set(v_reuseFailAlloc_2224_, 9, v_issues_2204_);
lean_ctor_set(v_reuseFailAlloc_2224_, 10, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2224_, 11, v_instanceOverrides_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*12, v_debug_2206_);
v___x_2219_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_st_ref_put(v_a_2146_, v___x_2219_);
if (v_isShared_2192_ == 0)
{
v___x_2222_ = v___x_2191_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2189_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2143_);
return v___y_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2282_, lean_object* v_snd_2283_, lean_object* v_a_2284_, uint8_t v___x_2285_, lean_object* v_fst_2286_, lean_object* v___x_2287_, lean_object* v_____r_2288_, uint8_t v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_arg_x27_2298_; lean_object* v___x_2332_; 
lean_inc_ref(v___x_2282_);
v___x_2332_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2287_, v_a_2284_, v___x_2282_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
switch(v___x_2334_)
{
case 0:
{
lean_object* v___x_2335_; 
lean_inc_ref(v___x_2282_);
v___x_2335_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2282_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v_arg_x27_2298_ = v_a_2336_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2337_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2335_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2335_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
case 1:
{
lean_object* v___x_2345_; 
lean_inc_ref(v___x_2282_);
v___x_2345_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2282_, v___y_2293_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_Expr_cleanupAnnotations(v_a_2346_);
v___x_2348_ = l_Lean_Expr_isApp(v___x_2347_);
if (v___x_2348_ == 0)
{
lean_dec_ref(v___x_2347_);
goto v___jp_2321_;
}
else
{
lean_object* v_arg_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_arg_2349_ = lean_ctor_get(v___x_2347_, 1);
lean_inc_ref(v_arg_2349_);
v___x_2350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2347_);
v___x_2351_ = l_Lean_Expr_isApp(v___x_2350_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_arg_2349_);
goto v___jp_2321_;
}
else
{
lean_object* v_arg_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_arg_2352_ = lean_ctor_get(v___x_2350_, 1);
lean_inc_ref(v_arg_2352_);
v___x_2353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2350_);
v___x_2354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2355_ = l_Lean_Expr_isConstOf(v___x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2357_ = l_Lean_Expr_isConstOf(v___x_2353_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec_ref(v___x_2353_);
lean_dec_ref(v_arg_2352_);
lean_dec_ref(v_arg_2349_);
goto v___jp_2321_;
}
else
{
lean_object* v___x_2358_; 
lean_inc_ref(v___x_2282_);
v___x_2358_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2353_, v_arg_2352_, v_arg_2349_, v___x_2282_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v_arg_x27_2298_ = v_a_2359_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
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
}
else
{
lean_object* v___x_2368_; 
lean_inc_ref(v___x_2282_);
v___x_2368_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2353_, v_arg_2352_, v_arg_2349_, v___x_2282_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v_arg_x27_2298_ = v_a_2369_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2370_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2368_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2368_);
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
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2378_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2345_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2345_);
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
default: 
{
goto v___jp_2310_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2386_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2332_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2332_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
v___jp_2297_:
{
size_t v___x_2299_; size_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2299_ = lean_ptr_addr(v___x_2282_);
lean_dec_ref(v___x_2282_);
v___x_2300_ = lean_ptr_addr(v_arg_x27_2298_);
v___x_2301_ = lean_usize_dec_eq(v___x_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_fst_2286_);
v___x_2302_ = lean_array_fset(v_snd_2283_, v_a_2284_, v_arg_x27_2298_);
v___x_2303_ = lean_box(v___x_2285_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2302_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec_ref(v_arg_x27_2298_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_fst_2286_);
lean_ctor_set(v___x_2307_, 1, v_snd_2283_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
v___jp_2310_:
{
lean_object* v___x_2311_; 
lean_inc_ref(v___x_2282_);
v___x_2311_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2282_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v_arg_x27_2298_ = v_a_2312_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2313_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2311_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2311_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
v___jp_2321_:
{
lean_object* v___x_2322_; 
lean_inc_ref(v___x_2282_);
v___x_2322_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2282_, v___x_2285_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v_arg_x27_2298_ = v_a_2323_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_fst_2286_);
lean_dec(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v_a_2324_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2322_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2398_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2399_ = l_Lean_Name_append(v___x_2398_, v___x_2397_);
return v___x_2399_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2402_ = l_Lean_stringToMessageData(v___x_2401_);
return v___x_2402_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2405_ = l_Lean_stringToMessageData(v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2409_, lean_object* v___x_2410_, lean_object* v_a_2411_, lean_object* v_b_2412_, uint8_t v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___y_2422_; uint8_t v___x_2444_; 
v___x_2444_ = lean_nat_dec_lt(v_a_2411_, v_upperBound_2409_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
lean_dec(v_a_2411_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_b_2412_);
return v___x_2445_;
}
else
{
lean_object* v_toCold_2446_; lean_object* v_options_2447_; lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2513_; 
v_toCold_2446_ = lean_ctor_get(v___y_2418_, 0);
v_options_2447_ = lean_ctor_get(v_toCold_2446_, 2);
v_fst_2448_ = lean_ctor_get(v_b_2412_, 0);
v_snd_2449_ = lean_ctor_get(v_b_2412_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_b_2412_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2451_ = v_b_2412_;
v_isShared_2452_ = v_isSharedCheck_2513_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_snd_2449_);
lean_inc(v_fst_2448_);
lean_dec(v_b_2412_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2513_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_inheritedTraceOptions_2453_; uint8_t v_hasTrace_2454_; lean_object* v___x_2455_; 
v_inheritedTraceOptions_2453_ = lean_ctor_get(v_toCold_2446_, 11);
v_hasTrace_2454_ = lean_ctor_get_uint8(v_options_2447_, sizeof(void*)*1);
v___x_2455_ = lean_array_fget(v_snd_2449_, v_a_2411_);
if (v_hasTrace_2454_ == 0)
{
lean_del_object(v___x_2451_);
goto v___jp_2456_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2460_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2453_, v_options_2447_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_del_object(v___x_2451_);
goto v___jp_2456_;
}
else
{
lean_object* v___x_2462_; 
lean_inc(v___x_2455_);
v___x_2462_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2410_, v_a_2411_, v___x_2455_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc(v___x_2455_);
v___x_2464_ = lean_infer_type(v___x_2455_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___y_2468_; uint8_t v___x_2492_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2492_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
switch(v___x_2492_)
{
case 0:
{
lean_object* v___x_2493_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2468_ = v___x_2493_;
goto v___jp_2467_;
}
case 1:
{
lean_object* v___x_2494_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2468_ = v___x_2494_;
goto v___jp_2467_;
}
case 2:
{
lean_object* v___x_2495_; 
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2468_ = v___x_2495_;
goto v___jp_2467_;
}
default: 
{
lean_object* v___x_2496_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2468_ = v___x_2496_;
goto v___jp_2467_;
}
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_inc(v___y_2468_);
v___x_2469_ = l_Lean_MessageData_ofFormat(v___y_2468_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 7);
lean_ctor_set(v___x_2451_, 1, v___x_2469_);
lean_ctor_set(v___x_2451_, 0, v___x_2466_);
v___x_2471_ = v___x_2451_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2472_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
lean_inc(v___x_2455_);
v___x_2474_ = l_Lean_MessageData_ofExpr(v___x_2455_);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l_Lean_MessageData_ofExpr(v_a_2465_);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2459_, v___x_2479_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2455_, v_snd_2449_, v_a_2411_, v___x_2444_, v_fst_2448_, v___x_2410_, v_a_2481_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
v___y_2422_ = v___x_2482_;
goto v___jp_2421_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v___x_2455_);
lean_dec(v_snd_2449_);
lean_dec(v_fst_2448_);
lean_dec(v_a_2411_);
v_a_2483_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2480_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2463_);
lean_dec(v___x_2455_);
lean_del_object(v___x_2451_);
lean_dec(v_snd_2449_);
lean_dec(v_fst_2448_);
lean_dec(v_a_2411_);
v_a_2497_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2464_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2464_);
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
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v___x_2455_);
lean_del_object(v___x_2451_);
lean_dec(v_snd_2449_);
lean_dec(v_fst_2448_);
lean_dec(v_a_2411_);
v_a_2505_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2462_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2462_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
v___jp_2456_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2455_, v_snd_2449_, v_a_2411_, v___x_2444_, v_fst_2448_, v___x_2410_, v___x_2457_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
v___y_2422_ = v___x_2458_;
goto v___jp_2421_;
}
}
}
v___jp_2421_:
{
if (lean_obj_tag(v___y_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2435_; 
v_a_2423_ = lean_ctor_get(v___y_2422_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___y_2422_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2425_ = v___y_2422_;
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___y_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
if (lean_obj_tag(v_a_2423_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; 
lean_dec(v_a_2411_);
v_a_2427_ = lean_ctor_get(v_a_2423_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v_a_2423_, 1);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v_a_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_del_object(v___x_2425_);
v_a_2431_ = lean_ctor_get(v_a_2423_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v_a_2423_, 1);
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_add(v_a_2411_, v___x_2432_);
lean_dec(v_a_2411_);
v_a_2411_ = v___x_2433_;
v_b_2412_ = v_a_2431_;
goto _start;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2411_);
v_a_2436_ = lean_ctor_get(v___y_2422_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___y_2422_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___y_2422_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___y_2422_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2514_, lean_object* v_x_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_, uint8_t v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___y_2527_; uint8_t v_modified_2528_; lean_object* v_f_2529_; uint8_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v_args_2585_; uint8_t v_modified_2586_; uint8_t v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; 
if (lean_obj_tag(v_x_2515_) == 5)
{
lean_object* v_fn_2622_; lean_object* v_arg_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_fn_2622_ = lean_ctor_get(v_x_2515_, 0);
lean_inc_ref(v_fn_2622_);
v_arg_2623_ = lean_ctor_get(v_x_2515_, 1);
lean_inc_ref(v_arg_2623_);
lean_dec_ref_known(v_x_2515_, 2);
v___x_2624_ = lean_array_set(v_x_2516_, v_x_2517_, v_arg_2623_);
v___x_2625_ = lean_unsigned_to_nat(1u);
v___x_2626_ = lean_nat_sub(v_x_2517_, v___x_2625_);
lean_dec(v_x_2517_);
v_x_2515_ = v_fn_2622_;
v_x_2516_ = v___x_2624_;
v_x_2517_ = v___x_2626_;
goto _start;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
lean_dec(v_x_2517_);
v___x_2628_ = lean_array_get_size(v_x_2516_);
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = lean_nat_dec_eq(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
v___y_2601_ = v___y_2518_;
v___y_2602_ = v___y_2519_;
v___y_2603_ = v___y_2520_;
v___y_2604_ = v___y_2521_;
v___y_2605_ = v___y_2522_;
v___y_2606_ = v___y_2523_;
v___y_2607_ = v___y_2524_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2631_ = l_Lean_instInhabitedExpr;
v___x_2632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___closed__1));
v___x_2633_ = l_Lean_Expr_isConstOf(v_x_2515_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2635_ = l_Lean_Expr_isConstOf(v_x_2515_, v___x_2634_);
if (v___x_2635_ == 0)
{
v___y_2601_ = v___y_2518_;
v___y_2602_ = v___y_2519_;
v___y_2603_ = v___y_2520_;
v___y_2604_ = v___y_2521_;
v___y_2605_ = v___y_2522_;
v___y_2606_ = v___y_2523_;
v___y_2607_ = v___y_2524_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_array_get(v___x_2631_, v_x_2516_, v___x_2636_);
v___x_2638_ = lean_unsigned_to_nat(1u);
v___x_2639_ = lean_array_get(v___x_2631_, v_x_2516_, v___x_2638_);
lean_dec_ref(v_x_2516_);
v___x_2640_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2515_, v___x_2637_, v___x_2639_, v_e_2514_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2640_;
}
}
else
{
lean_object* v___x_2641_; lean_object* v_prop_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v_prop_2642_ = lean_array_get_borrowed(v___x_2631_, v_x_2516_, v___x_2641_);
lean_inc(v_prop_2642_);
v___x_2643_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2642_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2660_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2660_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2660_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
size_t v___x_2648_; size_t v___x_2649_; uint8_t v___x_2650_; 
v___x_2648_ = lean_ptr_addr(v_prop_2642_);
v___x_2649_ = lean_ptr_addr(v_a_2644_);
v___x_2650_ = lean_usize_dec_eq(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_dec_ref(v_e_2514_);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_array_get(v___x_2631_, v_x_2516_, v___x_2651_);
lean_dec_ref(v_x_2516_);
v___x_2653_ = l_Lean_mkAppB(v_x_2515_, v_a_2644_, v___x_2652_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2653_);
v___x_2655_ = v___x_2646_;
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
else
{
lean_object* v___x_2658_; 
lean_dec(v_a_2644_);
lean_dec_ref(v_x_2516_);
lean_dec_ref(v_x_2515_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v_e_2514_);
v___x_2658_ = v___x_2646_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_e_2514_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_dec_ref(v_x_2516_);
lean_dec_ref(v_x_2515_);
lean_dec_ref(v_e_2514_);
return v___x_2643_;
}
}
}
}
v___jp_2526_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_box(0);
lean_inc_ref(v_f_2529_);
v___x_2538_ = l_Lean_Meta_getFunInfo(v_f_2529_, v___x_2537_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_paramInfo_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2574_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_paramInfo_2540_ = lean_ctor_get(v_a_2539_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v_a_2539_, 1);
lean_dec(v_unused_2575_);
v___x_2542_ = v_a_2539_;
v_isShared_2543_ = v_isSharedCheck_2574_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_paramInfo_2540_);
lean_dec(v_a_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2574_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2544_ = lean_array_get_size(v___y_2527_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_box(v_modified_2528_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v___y_2527_);
lean_ctor_set(v___x_2542_, 0, v___x_2546_);
v___x_2548_ = v___x_2542_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___y_2527_);
v___x_2548_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2544_, v_paramInfo_2540_, v___x_2545_, v___x_2548_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec_ref(v_paramInfo_2540_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2564_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_fst_2554_; uint8_t v___x_2555_; 
v_fst_2554_ = lean_ctor_get(v_a_2550_, 0);
v___x_2555_ = lean_unbox(v_fst_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2557_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_f_2529_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v_e_2514_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_e_2514_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
else
{
lean_object* v_snd_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec_ref(v_e_2514_);
v_snd_2559_ = lean_ctor_get(v_a_2550_, 1);
lean_inc(v_snd_2559_);
lean_dec(v_a_2550_);
v___x_2560_ = l_Lean_mkAppN(v_f_2529_, v_snd_2559_);
lean_dec(v_snd_2559_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2560_);
v___x_2562_ = v___x_2552_;
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
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_f_2529_);
lean_dec_ref(v_e_2514_);
v_a_2565_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2549_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2549_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec_ref(v_f_2529_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_e_2514_);
v_a_2576_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2538_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2538_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
v___jp_2584_:
{
lean_object* v___x_2594_; 
lean_inc_ref(v_x_2515_);
v___x_2594_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2515_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; size_t v___x_2596_; size_t v___x_2597_; uint8_t v___x_2598_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = lean_ptr_addr(v_x_2515_);
v___x_2597_ = lean_ptr_addr(v_a_2595_);
v___x_2598_ = lean_usize_dec_eq(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
uint8_t v___x_2599_; 
lean_dec_ref(v_x_2515_);
v___x_2599_ = 1;
v___y_2527_ = v_args_2585_;
v_modified_2528_ = v___x_2599_;
v_f_2529_ = v_a_2595_;
v___y_2530_ = v___y_2587_;
v___y_2531_ = v___y_2588_;
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2591_;
v___y_2535_ = v___y_2592_;
v___y_2536_ = v___y_2593_;
goto v___jp_2526_;
}
else
{
lean_dec(v_a_2595_);
v___y_2527_ = v_args_2585_;
v_modified_2528_ = v_modified_2586_;
v_f_2529_ = v_x_2515_;
v___y_2530_ = v___y_2587_;
v___y_2531_ = v___y_2588_;
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2591_;
v___y_2535_ = v___y_2592_;
v___y_2536_ = v___y_2593_;
goto v___jp_2526_;
}
}
else
{
lean_dec_ref(v_args_2585_);
lean_dec_ref(v_x_2515_);
lean_dec_ref(v_e_2514_);
return v___x_2594_;
}
}
v___jp_2600_:
{
uint8_t v_modified_2608_; lean_object* v___x_2609_; uint8_t v_modified_2610_; 
v_modified_2608_ = 0;
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2610_ = l_Lean_Expr_isConstOf(v_x_2515_, v___x_2609_);
if (v_modified_2610_ == 0)
{
v_args_2585_ = v_x_2516_;
v_modified_2586_ = v_modified_2608_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___y_2602_;
v___y_2589_ = v___y_2603_;
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___y_2605_;
v___y_2592_ = v___y_2606_;
v___y_2593_ = v___y_2607_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2611_; 
lean_inc_ref(v_x_2516_);
v___x_2611_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2516_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
if (lean_obj_tag(v_a_2612_) == 1)
{
lean_object* v_val_2613_; 
lean_dec_ref(v_x_2516_);
v_val_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v_a_2612_, 1);
v_args_2585_ = v_val_2613_;
v_modified_2586_ = v_modified_2610_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___y_2602_;
v___y_2589_ = v___y_2603_;
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___y_2605_;
v___y_2592_ = v___y_2606_;
v___y_2593_ = v___y_2607_;
goto v___jp_2584_;
}
else
{
lean_dec(v_a_2612_);
v_args_2585_ = v_x_2516_;
v_modified_2586_ = v_modified_2608_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___y_2602_;
v___y_2589_ = v___y_2603_;
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___y_2605_;
v___y_2592_ = v___y_2606_;
v___y_2593_ = v___y_2607_;
goto v___jp_2584_;
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v_x_2516_);
lean_dec_ref(v_x_2515_);
lean_dec_ref(v_e_2514_);
v_a_2614_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2611_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2611_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2661_, uint8_t v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_dummy_2670_; lean_object* v_nargs_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_dummy_2670_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2671_ = l_Lean_Expr_getAppNumArgs(v_e_2661_);
lean_inc(v_nargs_2671_);
v___x_2672_ = lean_mk_array(v_nargs_2671_, v_dummy_2670_);
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_sub(v_nargs_2671_, v___x_2673_);
lean_dec(v_nargs_2671_);
lean_inc_ref(v_e_2661_);
v___x_2675_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2661_, v_e_2661_, v___x_2672_, v___x_2674_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2676_, uint8_t v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v___x_2705_; 
lean_inc_ref(v_e_2676_);
v___x_2705_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2676_);
if (v___x_2705_ == 0)
{
lean_object* v_f_2706_; 
v_f_2706_ = l_Lean_Expr_getAppFn(v_e_2676_);
if (lean_obj_tag(v_f_2706_) == 4)
{
lean_object* v_declName_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_declName_2707_ = lean_ctor_get(v_f_2706_, 0);
lean_inc(v_declName_2707_);
lean_dec_ref_known(v_f_2706_, 2);
v___x_2708_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2709_ = lean_name_eq(v_declName_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_2711_ = lean_name_eq(v_declName_2707_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2713_ = lean_name_eq(v_declName_2707_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_2715_ = lean_name_eq(v_declName_2707_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_2717_ = lean_name_eq(v_declName_2707_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2707_, v_a_2683_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2748_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2748_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2748_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
if (lean_obj_tag(v_a_2719_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; 
lean_del_object(v___x_2721_);
v_val_2723_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v_a_2719_, 1);
lean_inc_ref(v_e_2676_);
v___x_2724_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2723_, v_e_2676_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_val_2723_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2736_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
if (lean_obj_tag(v_a_2725_) == 0)
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v_e_2676_);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_e_2676_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
else
{
lean_object* v_val_2732_; lean_object* v___x_2734_; 
lean_dec_ref(v_e_2676_);
v_val_2732_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v_a_2725_, 1);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v_val_2732_);
v___x_2734_ = v___x_2727_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_val_2732_);
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
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_e_2676_);
v_a_2737_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2724_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2724_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
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
else
{
lean_object* v___x_2746_; 
lean_dec(v_a_2719_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v_e_2676_);
v___x_2746_ = v___x_2721_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_e_2676_);
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
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_e_2676_);
v_a_2749_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2718_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2718_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_dec(v_declName_2707_);
goto v___jp_2685_;
}
}
else
{
lean_dec(v_declName_2707_);
goto v___jp_2685_;
}
}
else
{
lean_dec(v_declName_2707_);
goto v___jp_2685_;
}
}
else
{
lean_dec(v_declName_2707_);
goto v___jp_2685_;
}
}
else
{
lean_dec(v_declName_2707_);
goto v___jp_2685_;
}
}
else
{
lean_object* v___x_2757_; 
lean_dec_ref(v_f_2706_);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_e_2676_);
return v___x_2757_;
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_inc_ref(v_e_2676_);
v___x_2758_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2758_, 0, v_e_2676_);
v___x_2759_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2758_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2793_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2793_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2793_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_dec_ref(v_e_2676_);
v_val_2764_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_a_2760_, 1);
v___x_2765_ = l_Lean_mkNatLit(v_val_2764_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2765_);
v___x_2767_ = v___x_2762_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v___x_2769_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_inc_ref(v_e_2676_);
v___x_2769_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2676_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2784_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2784_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2784_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
if (lean_obj_tag(v_a_2770_) == 1)
{
lean_object* v_val_2774_; lean_object* v_fst_2775_; lean_object* v_snd_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec_ref(v_e_2676_);
v_val_2774_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v_a_2770_, 1);
v_fst_2775_ = lean_ctor_get(v_val_2774_, 0);
lean_inc(v_fst_2775_);
v_snd_2776_ = lean_ctor_get(v_val_2774_, 1);
lean_inc(v_snd_2776_);
lean_dec(v_val_2774_);
v___x_2777_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2775_, v_snd_2776_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2777_);
v___x_2779_ = v___x_2772_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
lean_object* v___x_2782_; 
lean_dec(v_a_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_e_2676_);
v___x_2782_ = v___x_2772_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_e_2676_);
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
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_e_2676_);
v_a_2785_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2769_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2769_);
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
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v_e_2676_);
v_a_2794_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2759_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2759_);
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
v___jp_2685_:
{
lean_object* v___x_2686_; 
lean_inc_ref(v_e_2676_);
v___x_2686_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2676_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2696_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
if (lean_obj_tag(v_a_2687_) == 1)
{
lean_object* v_val_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2689_);
lean_dec_ref(v_e_2676_);
v_val_2691_ = lean_ctor_get(v_a_2687_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v_a_2687_, 1);
v___x_2692_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2691_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
return v___x_2692_;
}
else
{
lean_object* v___x_2694_; 
lean_dec(v_a_2687_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_e_2676_);
v___x_2694_ = v___x_2689_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_e_2676_);
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
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_e_2676_);
v_a_2697_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2686_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2686_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2802_, uint8_t v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2812_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2813_;
}
else
{
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2814_, uint8_t v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2814_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
if (lean_obj_tag(v_a_2824_) == 0)
{
lean_object* v_val_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v_e_2814_);
v_val_2825_ = lean_ctor_get(v_a_2824_, 0);
lean_inc_ref(v_val_2825_);
lean_dec_ref_known(v_a_2824_, 1);
v___x_2826_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2825_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; 
lean_dec(v_a_2824_);
v___x_2827_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2828_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2839_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2839_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2839_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
if (lean_obj_tag(v_a_2830_) == 0)
{
lean_object* v_val_2834_; lean_object* v___x_2835_; 
lean_del_object(v___x_2832_);
lean_dec(v_a_2828_);
v_val_2834_ = lean_ctor_get(v_a_2830_, 0);
lean_inc_ref(v_val_2834_);
lean_dec_ref_known(v_a_2830_, 1);
v___x_2835_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2834_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2835_;
}
else
{
lean_object* v___x_2837_; 
lean_dec(v_a_2830_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v_a_2828_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2828_);
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
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2828_);
v_a_2840_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2829_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2829_);
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
else
{
return v___x_2827_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v_e_2814_);
v_a_2848_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2823_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2823_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2862_, uint8_t v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
uint8_t v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___x_2881_; 
lean_inc_ref(v_e_2862_);
v___x_2881_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2862_, v_a_2867_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = l_Lean_Expr_cleanupAnnotations(v_a_2882_);
v___x_2884_ = l_Lean_Expr_isApp(v___x_2883_);
if (v___x_2884_ == 0)
{
lean_dec_ref(v___x_2883_);
v___y_2872_ = v_a_2863_;
v___y_2873_ = v_a_2864_;
v___y_2874_ = v_a_2865_;
v___y_2875_ = v_a_2866_;
v___y_2876_ = v_a_2867_;
v___y_2877_ = v_a_2868_;
v___y_2878_ = v_a_2869_;
goto v___jp_2871_;
}
else
{
lean_object* v_arg_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_arg_2885_ = lean_ctor_get(v___x_2883_, 1);
lean_inc_ref(v_arg_2885_);
v___x_2886_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2883_);
v___x_2887_ = l_Lean_Expr_isApp(v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec_ref(v___x_2886_);
lean_dec_ref(v_arg_2885_);
v___y_2872_ = v_a_2863_;
v___y_2873_ = v_a_2864_;
v___y_2874_ = v_a_2865_;
v___y_2875_ = v_a_2866_;
v___y_2876_ = v_a_2867_;
v___y_2877_ = v_a_2868_;
v___y_2878_ = v_a_2869_;
goto v___jp_2871_;
}
else
{
lean_object* v_arg_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_arg_2888_ = lean_ctor_get(v___x_2886_, 1);
lean_inc_ref(v_arg_2888_);
v___x_2889_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2886_);
v___x_2890_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2891_ = l_Lean_Expr_isConstOf(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v___x_2889_);
lean_dec_ref(v_arg_2888_);
lean_dec_ref(v_arg_2885_);
v___y_2872_ = v_a_2863_;
v___y_2873_ = v_a_2864_;
v___y_2874_ = v_a_2865_;
v___y_2875_ = v_a_2866_;
v___y_2876_ = v_a_2867_;
v___y_2877_ = v_a_2868_;
v___y_2878_ = v_a_2869_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2889_, v_arg_2888_, v_arg_2885_, v_e_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2892_;
}
}
}
}
else
{
lean_dec_ref(v_e_2862_);
return v___x_2881_;
}
v___jp_2871_:
{
uint8_t v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = 0;
v___x_2880_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2862_, v___x_2879_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2893_, lean_object* v_00_u03b1_2894_, lean_object* v_c_2895_, lean_object* v_inst_2896_, lean_object* v_a_2897_, lean_object* v_b_2898_, uint8_t v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2895_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; uint8_t v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_n(v_a_2908_, 2);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2908_);
if (v___x_2909_ == 0)
{
uint8_t v___x_2910_; 
lean_inc(v_a_2908_);
v___x_2910_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2908_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2894_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2896_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2897_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = l_Lean_mkApp5(v_f_2893_, v_a_2912_, v_a_2908_, v_a_2914_, v_a_2916_, v_a_2918_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v___x_2922_);
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
else
{
lean_dec(v_a_2916_);
lean_dec(v_a_2914_);
lean_dec(v_a_2912_);
lean_dec(v_a_2908_);
lean_dec_ref(v_f_2893_);
return v___x_2917_;
}
}
else
{
lean_dec(v_a_2914_);
lean_dec(v_a_2912_);
lean_dec(v_a_2908_);
lean_dec_ref(v_b_2898_);
lean_dec_ref(v_f_2893_);
return v___x_2915_;
}
}
else
{
lean_dec(v_a_2912_);
lean_dec(v_a_2908_);
lean_dec_ref(v_b_2898_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_f_2893_);
return v___x_2913_;
}
}
else
{
lean_dec(v_a_2908_);
lean_dec_ref(v_b_2898_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_inst_2896_);
lean_dec_ref(v_f_2893_);
return v___x_2911_;
}
}
else
{
lean_object* v___x_2927_; 
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_inst_2896_);
lean_dec_ref(v_00_u03b1_2894_);
lean_dec_ref(v_f_2893_);
v___x_2927_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
return v___x_2927_;
}
}
else
{
lean_object* v___x_2928_; 
lean_dec(v_a_2908_);
lean_dec_ref(v_b_2898_);
lean_dec_ref(v_inst_2896_);
lean_dec_ref(v_00_u03b1_2894_);
lean_dec_ref(v_f_2893_);
v___x_2928_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2897_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
return v___x_2928_;
}
}
else
{
lean_dec_ref(v_b_2898_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_inst_2896_);
lean_dec_ref(v_00_u03b1_2894_);
lean_dec_ref(v_f_2893_);
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2929_, lean_object* v_00_u03b1_2930_, lean_object* v_c_2931_, lean_object* v_a_2932_, lean_object* v_b_2933_, uint8_t v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2931_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; uint8_t v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_n(v_a_2943_, 2);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = l_Lean_Expr_isBoolTrue(v_a_2943_);
if (v___x_2944_ == 0)
{
uint8_t v___x_2945_; 
lean_inc(v_a_2943_);
v___x_2945_ = l_Lean_Expr_isBoolFalse(v_a_2943_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
v___x_2946_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2930_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2932_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2959_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2959_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2959_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2955_ = l_Lean_mkApp4(v_f_2929_, v_a_2947_, v_a_2943_, v_a_2949_, v_a_2951_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2943_);
lean_dec_ref(v_f_2929_);
return v___x_2950_;
}
}
else
{
lean_dec(v_a_2947_);
lean_dec(v_a_2943_);
lean_dec_ref(v_b_2933_);
lean_dec_ref(v_f_2929_);
return v___x_2948_;
}
}
else
{
lean_dec(v_a_2943_);
lean_dec_ref(v_b_2933_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_f_2929_);
return v___x_2946_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_00_u03b1_2930_);
lean_dec_ref(v_f_2929_);
v___x_2960_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2960_;
}
}
else
{
lean_object* v___x_2961_; 
lean_dec(v_a_2943_);
lean_dec_ref(v_b_2933_);
lean_dec_ref(v_00_u03b1_2930_);
lean_dec_ref(v_f_2929_);
v___x_2961_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2932_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2961_;
}
}
else
{
lean_dec_ref(v_b_2933_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_00_u03b1_2930_);
lean_dec_ref(v_f_2929_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2962_, uint8_t v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; uint8_t v___y_2980_; uint8_t v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___x_3008_; 
lean_inc_ref(v_e_2962_);
v___x_3008_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2962_, v_a_2967_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Expr_cleanupAnnotations(v_a_3009_);
v___x_3011_ = l_Lean_Expr_isApp(v___x_3010_);
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v_arg_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_arg_3012_ = lean_ctor_get(v___x_3010_, 1);
lean_inc_ref(v_arg_3012_);
v___x_3013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3010_);
v___x_3014_ = l_Lean_Expr_isApp(v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec_ref(v___x_3013_);
lean_dec_ref(v_arg_3012_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v_arg_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v_arg_3015_ = lean_ctor_get(v___x_3013_, 1);
lean_inc_ref(v_arg_3015_);
v___x_3016_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3013_);
v___x_3017_ = l_Lean_Expr_isApp(v___x_3016_);
if (v___x_3017_ == 0)
{
lean_dec_ref(v___x_3016_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v_arg_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_arg_3018_ = lean_ctor_get(v___x_3016_, 1);
lean_inc_ref(v_arg_3018_);
v___x_3019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3016_);
v___x_3020_ = l_Lean_Expr_isApp(v___x_3019_);
if (v___x_3020_ == 0)
{
lean_dec_ref(v___x_3019_);
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v_arg_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v_arg_3021_ = lean_ctor_get(v___x_3019_, 1);
lean_inc_ref(v_arg_3021_);
v___x_3022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3019_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3024_ = l_Lean_Expr_isConstOf(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = l_Lean_Expr_isApp(v___x_3022_);
if (v___x_3025_ == 0)
{
lean_dec_ref(v___x_3022_);
lean_dec_ref(v_arg_3021_);
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v_arg_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v_arg_3026_ = lean_ctor_get(v___x_3022_, 1);
lean_inc_ref(v_arg_3026_);
v___x_3027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3022_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3029_ = l_Lean_Expr_isConstOf(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_dec_ref(v___x_3027_);
lean_dec_ref(v_arg_3026_);
lean_dec_ref(v_arg_3021_);
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
v___y_2999_ = v_a_2963_;
v___y_3000_ = v_a_2964_;
v___y_3001_ = v_a_2965_;
v___y_3002_ = v_a_2966_;
v___y_3003_ = v_a_2967_;
v___y_3004_ = v_a_2968_;
v___y_3005_ = v_a_2969_;
goto v___jp_2998_;
}
else
{
lean_object* v___x_3030_; 
lean_dec_ref(v_e_2962_);
v___x_3030_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3027_, v_arg_3026_, v_arg_3021_, v_arg_3018_, v_arg_3015_, v_arg_3012_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
return v___x_3030_;
}
}
}
else
{
lean_object* v___x_3031_; 
lean_dec_ref(v_e_2962_);
v___x_3031_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3022_, v_arg_3021_, v_arg_3018_, v_arg_3015_, v_arg_3012_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
return v___x_3031_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2962_);
return v___x_3008_;
}
v___jp_2971_:
{
if (v___y_2980_ == 0)
{
if (lean_obj_tag(v___y_2974_) == 4)
{
lean_object* v_declName_2981_; lean_object* v___x_2982_; 
v_declName_2981_ = lean_ctor_get(v___y_2974_, 0);
lean_inc(v_declName_2981_);
lean_dec_ref_known(v___y_2974_, 2);
v___x_2982_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2981_, v___y_2972_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; uint8_t v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = lean_unbox(v_a_2983_);
lean_dec(v_a_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2962_, v___y_2977_, v___y_2978_, v___y_2973_, v___y_2979_, v___y_2976_, v___y_2975_, v___y_2972_);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2962_, v___y_2977_, v___y_2978_, v___y_2973_, v___y_2979_, v___y_2976_, v___y_2975_, v___y_2972_);
return v___x_2986_;
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v_e_2962_);
v_a_2987_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2982_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2982_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v___x_2995_; 
lean_dec_ref(v___y_2974_);
v___x_2995_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2962_, v___y_2977_, v___y_2978_, v___y_2973_, v___y_2979_, v___y_2976_, v___y_2975_, v___y_2972_);
return v___x_2995_;
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_dec_ref(v___y_2974_);
v___x_2996_ = l_Lean_Expr_headBeta(v_e_2962_);
v___x_2997_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2996_, v___y_2977_, v___y_2978_, v___y_2973_, v___y_2979_, v___y_2976_, v___y_2975_, v___y_2972_);
return v___x_2997_;
}
}
v___jp_2998_:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = l_Lean_Expr_getAppFn(v_e_2962_);
v___x_3007_ = l_Lean_Expr_isLambda(v___x_3006_);
if (v___x_3007_ == 0)
{
v___y_2972_ = v___y_3005_;
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___x_3006_;
v___y_2975_ = v___y_3004_;
v___y_2976_ = v___y_3003_;
v___y_2977_ = v___y_2999_;
v___y_2978_ = v___y_3000_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___x_3007_;
goto v___jp_2971_;
}
else
{
v___y_2972_ = v___y_3005_;
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___x_3006_;
v___y_2975_ = v___y_3004_;
v___y_2976_ = v___y_3003_;
v___y_2977_ = v___y_2999_;
v___y_2978_ = v___y_3000_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___y_2999_;
goto v___jp_2971_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3036_ = lean_unsigned_to_nat(18u);
v___x_3037_ = lean_unsigned_to_nat(1913u);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3039_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3040_ = l_mkPanicMessageWithDecl(v___x_3039_, v___x_3038_, v___x_3037_, v___x_3036_, v___x_3035_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3041_, uint8_t v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = l_Lean_Expr_projExpr_x21(v_e_3041_);
v___x_3051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3050_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___y_3054_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
if (lean_obj_tag(v_e_3041_) == 11)
{
lean_object* v_typeName_3076_; lean_object* v_idx_3077_; lean_object* v_struct_3078_; size_t v___x_3079_; size_t v___x_3080_; uint8_t v___x_3081_; 
v_typeName_3076_ = lean_ctor_get(v_e_3041_, 0);
v_idx_3077_ = lean_ctor_get(v_e_3041_, 1);
v_struct_3078_ = lean_ctor_get(v_e_3041_, 2);
v___x_3079_ = lean_ptr_addr(v_struct_3078_);
v___x_3080_ = lean_ptr_addr(v_a_3052_);
v___x_3081_ = lean_usize_dec_eq(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_inc(v_idx_3077_);
lean_inc(v_typeName_3076_);
lean_dec_ref_known(v_e_3041_, 3);
v___x_3082_ = l_Lean_Expr_proj___override(v_typeName_3076_, v_idx_3077_, v_a_3052_);
v___y_3054_ = v___x_3082_;
goto v___jp_3053_;
}
else
{
lean_dec(v_a_3052_);
v___y_3054_ = v_e_3041_;
goto v___jp_3053_;
}
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
lean_dec(v_a_3052_);
lean_dec_ref(v_e_3041_);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3084_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3083_);
v___y_3054_ = v___x_3084_;
goto v___jp_3053_;
}
v___jp_3053_:
{
lean_object* v___x_3055_; 
lean_inc_ref(v___y_3054_);
v___x_3055_ = l_Lean_Meta_reduceProj_x3f(v___y_3054_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3067_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3067_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3067_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
if (lean_obj_tag(v_a_3056_) == 0)
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___y_3054_);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___y_3054_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3065_; 
lean_dec_ref(v___y_3054_);
v_val_3063_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_val_3063_);
lean_dec_ref_known(v_a_3056_, 1);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v_val_3063_);
v___x_3065_ = v___x_3058_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_val_3063_);
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
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___y_3054_);
v_a_3068_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3055_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3055_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3041_);
return v___x_3051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3085_, uint8_t v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
switch(lean_obj_tag(v_e_3085_))
{
case 7:
{
lean_object* v___x_3094_; 
v___x_3094_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3086_ == 0)
{
lean_object* v___x_3095_; lean_object* v_canon_3096_; lean_object* v_cache_3097_; lean_object* v___x_3098_; 
v___x_3095_ = lean_st_ref_get(v_a_3088_);
v_canon_3096_ = lean_ctor_get(v___x_3095_, 10);
lean_inc_ref(v_canon_3096_);
lean_dec(v___x_3095_);
v_cache_3097_ = lean_ctor_get(v_canon_3096_, 0);
lean_inc_ref(v_cache_3097_);
lean_dec_ref(v_canon_3096_);
v___x_3098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3097_, v_e_3085_);
lean_dec_ref(v_cache_3097_);
if (lean_obj_tag(v___x_3098_) == 1)
{
lean_object* v_val_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref_known(v_e_3085_, 3);
v_val_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_val_3099_);
lean_dec(v___x_3098_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 0);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_val_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v___x_3107_; 
lean_dec(v___x_3098_);
lean_inc_ref(v_e_3085_);
v___x_3107_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3094_, v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3147_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3147_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3147_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v_canon_3113_; lean_object* v_share_3114_; lean_object* v_maxFVar_3115_; lean_object* v_proofInstInfo_3116_; lean_object* v_proofInstInfoFVar_3117_; lean_object* v_inferType_3118_; lean_object* v_getLevel_3119_; lean_object* v_congrInfo_3120_; lean_object* v_defEqI_3121_; lean_object* v_extensions_3122_; lean_object* v_issues_3123_; lean_object* v_instanceOverrides_3124_; uint8_t v_debug_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3146_; 
v___x_3112_ = lean_st_ref_take(v_a_3088_);
v_canon_3113_ = lean_ctor_get(v___x_3112_, 10);
v_share_3114_ = lean_ctor_get(v___x_3112_, 0);
v_maxFVar_3115_ = lean_ctor_get(v___x_3112_, 1);
v_proofInstInfo_3116_ = lean_ctor_get(v___x_3112_, 2);
v_proofInstInfoFVar_3117_ = lean_ctor_get(v___x_3112_, 3);
v_inferType_3118_ = lean_ctor_get(v___x_3112_, 4);
v_getLevel_3119_ = lean_ctor_get(v___x_3112_, 5);
v_congrInfo_3120_ = lean_ctor_get(v___x_3112_, 6);
v_defEqI_3121_ = lean_ctor_get(v___x_3112_, 7);
v_extensions_3122_ = lean_ctor_get(v___x_3112_, 8);
v_issues_3123_ = lean_ctor_get(v___x_3112_, 9);
v_instanceOverrides_3124_ = lean_ctor_get(v___x_3112_, 11);
v_debug_3125_ = lean_ctor_get_uint8(v___x_3112_, sizeof(void*)*12);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3127_ = v___x_3112_;
v_isShared_3128_ = v_isSharedCheck_3146_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_instanceOverrides_3124_);
lean_inc(v_canon_3113_);
lean_inc(v_issues_3123_);
lean_inc(v_extensions_3122_);
lean_inc(v_defEqI_3121_);
lean_inc(v_congrInfo_3120_);
lean_inc(v_getLevel_3119_);
lean_inc(v_inferType_3118_);
lean_inc(v_proofInstInfoFVar_3117_);
lean_inc(v_proofInstInfo_3116_);
lean_inc(v_maxFVar_3115_);
lean_inc(v_share_3114_);
lean_dec(v___x_3112_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3146_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v_cache_3129_; lean_object* v_cacheInType_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3145_; 
v_cache_3129_ = lean_ctor_get(v_canon_3113_, 0);
v_cacheInType_3130_ = lean_ctor_get(v_canon_3113_, 1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_canon_3113_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3132_ = v_canon_3113_;
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_cacheInType_3130_);
lean_inc(v_cache_3129_);
lean_dec(v_canon_3113_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_inc(v_a_3108_);
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3129_, v_e_3085_, v_a_3108_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3134_);
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_cacheInType_3130_);
v___x_3136_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 10, v___x_3136_);
v___x_3138_ = v___x_3127_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_share_3114_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_maxFVar_3115_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_proofInstInfo_3116_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_proofInstInfoFVar_3117_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_inferType_3118_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v_getLevel_3119_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_congrInfo_3120_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_defEqI_3121_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_extensions_3122_);
lean_ctor_set(v_reuseFailAlloc_3143_, 9, v_issues_3123_);
lean_ctor_set(v_reuseFailAlloc_3143_, 10, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3143_, 11, v_instanceOverrides_3124_);
lean_ctor_set_uint8(v_reuseFailAlloc_3143_, sizeof(void*)*12, v_debug_3125_);
v___x_3138_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_st_ref_put(v_a_3088_, v___x_3138_);
if (v_isShared_3111_ == 0)
{
v___x_3141_ = v___x_3110_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3108_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3107_;
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v_canon_3149_; lean_object* v_cacheInType_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_st_ref_get(v_a_3088_);
v_canon_3149_ = lean_ctor_get(v___x_3148_, 10);
lean_inc_ref(v_canon_3149_);
lean_dec(v___x_3148_);
v_cacheInType_3150_ = lean_ctor_get(v_canon_3149_, 1);
lean_inc_ref(v_cacheInType_3150_);
lean_dec_ref(v_canon_3149_);
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3150_, v_e_3085_);
lean_dec_ref(v_cacheInType_3150_);
if (lean_obj_tag(v___x_3151_) == 1)
{
lean_object* v_val_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref_known(v_e_3085_, 3);
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
lean_inc_ref(v_e_3085_);
v___x_3160_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3094_, v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3165_ = lean_st_ref_take(v_a_3088_);
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
v___x_3187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3183_, v_e_3085_, v_a_3161_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_cache_3182_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3187_);
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
v___x_3192_ = lean_st_ref_put(v_a_3088_, v___x_3191_);
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
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3160_;
}
}
}
}
case 6:
{
if (v_a_3086_ == 0)
{
lean_object* v___x_3201_; lean_object* v_canon_3202_; lean_object* v_cache_3203_; lean_object* v___x_3204_; 
v___x_3201_ = lean_st_ref_get(v_a_3088_);
v_canon_3202_ = lean_ctor_get(v___x_3201_, 10);
lean_inc_ref(v_canon_3202_);
lean_dec(v___x_3201_);
v_cache_3203_ = lean_ctor_get(v_canon_3202_, 0);
lean_inc_ref(v_cache_3203_);
lean_dec_ref(v_canon_3202_);
v___x_3204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3203_, v_e_3085_);
lean_dec_ref(v_cache_3203_);
if (lean_obj_tag(v___x_3204_) == 1)
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref_known(v_e_3085_, 3);
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
lean_inc_ref(v_e_3085_);
v___x_3213_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3218_ = lean_st_ref_take(v_a_3088_);
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
v___x_3240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3235_, v_e_3085_, v_a_3214_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_cacheInType_3236_);
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
v___x_3245_ = lean_st_ref_put(v_a_3088_, v___x_3244_);
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
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3213_;
}
}
}
else
{
lean_object* v___x_3254_; lean_object* v_canon_3255_; lean_object* v_cacheInType_3256_; lean_object* v___x_3257_; 
v___x_3254_ = lean_st_ref_get(v_a_3088_);
v_canon_3255_ = lean_ctor_get(v___x_3254_, 10);
lean_inc_ref(v_canon_3255_);
lean_dec(v___x_3254_);
v_cacheInType_3256_ = lean_ctor_get(v_canon_3255_, 1);
lean_inc_ref(v_cacheInType_3256_);
lean_dec_ref(v_canon_3255_);
v___x_3257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3256_, v_e_3085_);
lean_dec_ref(v_cacheInType_3256_);
if (lean_obj_tag(v___x_3257_) == 1)
{
lean_object* v_val_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref_known(v_e_3085_, 3);
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
lean_inc_ref(v_e_3085_);
v___x_3266_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3271_ = lean_st_ref_take(v_a_3088_);
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
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3289_, v_e_3085_, v_a_3267_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_cache_3288_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3293_);
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
v___x_3298_ = lean_st_ref_put(v_a_3088_, v___x_3297_);
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
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3266_;
}
}
}
}
case 8:
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3086_ == 0)
{
lean_object* v___x_3308_; lean_object* v_canon_3309_; lean_object* v_cache_3310_; lean_object* v___x_3311_; 
v___x_3308_ = lean_st_ref_get(v_a_3088_);
v_canon_3309_ = lean_ctor_get(v___x_3308_, 10);
lean_inc_ref(v_canon_3309_);
lean_dec(v___x_3308_);
v_cache_3310_ = lean_ctor_get(v_canon_3309_, 0);
lean_inc_ref(v_cache_3310_);
lean_dec_ref(v_canon_3309_);
v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3310_, v_e_3085_);
lean_dec_ref(v_cache_3310_);
if (lean_obj_tag(v___x_3311_) == 1)
{
lean_object* v_val_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec_ref_known(v_e_3085_, 4);
v_val_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_val_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_val_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
else
{
lean_object* v___x_3320_; 
lean_dec(v___x_3311_);
lean_inc_ref(v_e_3085_);
v___x_3320_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3307_, v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3360_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3360_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3360_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v_canon_3326_; lean_object* v_share_3327_; lean_object* v_maxFVar_3328_; lean_object* v_proofInstInfo_3329_; lean_object* v_proofInstInfoFVar_3330_; lean_object* v_inferType_3331_; lean_object* v_getLevel_3332_; lean_object* v_congrInfo_3333_; lean_object* v_defEqI_3334_; lean_object* v_extensions_3335_; lean_object* v_issues_3336_; lean_object* v_instanceOverrides_3337_; uint8_t v_debug_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3359_; 
v___x_3325_ = lean_st_ref_take(v_a_3088_);
v_canon_3326_ = lean_ctor_get(v___x_3325_, 10);
v_share_3327_ = lean_ctor_get(v___x_3325_, 0);
v_maxFVar_3328_ = lean_ctor_get(v___x_3325_, 1);
v_proofInstInfo_3329_ = lean_ctor_get(v___x_3325_, 2);
v_proofInstInfoFVar_3330_ = lean_ctor_get(v___x_3325_, 3);
v_inferType_3331_ = lean_ctor_get(v___x_3325_, 4);
v_getLevel_3332_ = lean_ctor_get(v___x_3325_, 5);
v_congrInfo_3333_ = lean_ctor_get(v___x_3325_, 6);
v_defEqI_3334_ = lean_ctor_get(v___x_3325_, 7);
v_extensions_3335_ = lean_ctor_get(v___x_3325_, 8);
v_issues_3336_ = lean_ctor_get(v___x_3325_, 9);
v_instanceOverrides_3337_ = lean_ctor_get(v___x_3325_, 11);
v_debug_3338_ = lean_ctor_get_uint8(v___x_3325_, sizeof(void*)*12);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3340_ = v___x_3325_;
v_isShared_3341_ = v_isSharedCheck_3359_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_instanceOverrides_3337_);
lean_inc(v_canon_3326_);
lean_inc(v_issues_3336_);
lean_inc(v_extensions_3335_);
lean_inc(v_defEqI_3334_);
lean_inc(v_congrInfo_3333_);
lean_inc(v_getLevel_3332_);
lean_inc(v_inferType_3331_);
lean_inc(v_proofInstInfoFVar_3330_);
lean_inc(v_proofInstInfo_3329_);
lean_inc(v_maxFVar_3328_);
lean_inc(v_share_3327_);
lean_dec(v___x_3325_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3359_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_cache_3342_; lean_object* v_cacheInType_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3358_; 
v_cache_3342_ = lean_ctor_get(v_canon_3326_, 0);
v_cacheInType_3343_ = lean_ctor_get(v_canon_3326_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_canon_3326_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3345_ = v_canon_3326_;
v_isShared_3346_ = v_isSharedCheck_3358_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_cacheInType_3343_);
lean_inc(v_cache_3342_);
lean_dec(v_canon_3326_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3358_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_inc(v_a_3321_);
v___x_3347_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3342_, v_e_3085_, v_a_3321_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_cacheInType_3343_);
v___x_3349_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 10, v___x_3349_);
v___x_3351_ = v___x_3340_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_share_3327_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_maxFVar_3328_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_proofInstInfo_3329_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v_proofInstInfoFVar_3330_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v_inferType_3331_);
lean_ctor_set(v_reuseFailAlloc_3356_, 5, v_getLevel_3332_);
lean_ctor_set(v_reuseFailAlloc_3356_, 6, v_congrInfo_3333_);
lean_ctor_set(v_reuseFailAlloc_3356_, 7, v_defEqI_3334_);
lean_ctor_set(v_reuseFailAlloc_3356_, 8, v_extensions_3335_);
lean_ctor_set(v_reuseFailAlloc_3356_, 9, v_issues_3336_);
lean_ctor_set(v_reuseFailAlloc_3356_, 10, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3356_, 11, v_instanceOverrides_3337_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, sizeof(void*)*12, v_debug_3338_);
v___x_3351_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3352_ = lean_st_ref_put(v_a_3088_, v___x_3351_);
if (v_isShared_3324_ == 0)
{
v___x_3354_ = v___x_3323_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3321_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3085_, 4);
return v___x_3320_;
}
}
}
else
{
lean_object* v___x_3361_; lean_object* v_canon_3362_; lean_object* v_cacheInType_3363_; lean_object* v___x_3364_; 
v___x_3361_ = lean_st_ref_get(v_a_3088_);
v_canon_3362_ = lean_ctor_get(v___x_3361_, 10);
lean_inc_ref(v_canon_3362_);
lean_dec(v___x_3361_);
v_cacheInType_3363_ = lean_ctor_get(v_canon_3362_, 1);
lean_inc_ref(v_cacheInType_3363_);
lean_dec_ref(v_canon_3362_);
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3363_, v_e_3085_);
lean_dec_ref(v_cacheInType_3363_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref_known(v_e_3085_, 4);
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
lean_inc_ref(v_e_3085_);
v___x_3373_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3307_, v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3378_ = lean_st_ref_take(v_a_3088_);
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
v___x_3400_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3396_, v_e_3085_, v_a_3374_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 1, v___x_3400_);
v___x_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_cache_3395_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3400_);
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
v___x_3405_ = lean_st_ref_put(v_a_3088_, v___x_3404_);
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
lean_dec_ref_known(v_e_3085_, 4);
return v___x_3373_;
}
}
}
}
case 5:
{
if (v_a_3086_ == 0)
{
lean_object* v___x_3414_; lean_object* v_canon_3415_; lean_object* v_cache_3416_; lean_object* v___x_3417_; 
v___x_3414_ = lean_st_ref_get(v_a_3088_);
v_canon_3415_ = lean_ctor_get(v___x_3414_, 10);
lean_inc_ref(v_canon_3415_);
lean_dec(v___x_3414_);
v_cache_3416_ = lean_ctor_get(v_canon_3415_, 0);
lean_inc_ref(v_cache_3416_);
lean_dec_ref(v_canon_3415_);
v___x_3417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3416_, v_e_3085_);
lean_dec_ref(v_cache_3416_);
if (lean_obj_tag(v___x_3417_) == 1)
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref_known(v_e_3085_, 2);
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
lean_inc_ref(v_e_3085_);
v___x_3426_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3431_ = lean_st_ref_take(v_a_3088_);
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
v___x_3453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3448_, v_e_3085_, v_a_3427_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_cacheInType_3449_);
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
v___x_3458_ = lean_st_ref_put(v_a_3088_, v___x_3457_);
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
lean_dec_ref_known(v_e_3085_, 2);
return v___x_3426_;
}
}
}
else
{
lean_object* v___x_3467_; lean_object* v_canon_3468_; lean_object* v_cacheInType_3469_; lean_object* v___x_3470_; 
v___x_3467_ = lean_st_ref_get(v_a_3088_);
v_canon_3468_ = lean_ctor_get(v___x_3467_, 10);
lean_inc_ref(v_canon_3468_);
lean_dec(v___x_3467_);
v_cacheInType_3469_ = lean_ctor_get(v_canon_3468_, 1);
lean_inc_ref(v_cacheInType_3469_);
lean_dec_ref(v_canon_3468_);
v___x_3470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3469_, v_e_3085_);
lean_dec_ref(v_cacheInType_3469_);
if (lean_obj_tag(v___x_3470_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref_known(v_e_3085_, 2);
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
lean_inc_ref(v_e_3085_);
v___x_3479_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3484_ = lean_st_ref_take(v_a_3088_);
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
v___x_3506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3502_, v_e_3085_, v_a_3480_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_cache_3501_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3506_);
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
v___x_3511_ = lean_st_ref_put(v_a_3088_, v___x_3510_);
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
lean_dec_ref_known(v_e_3085_, 2);
return v___x_3479_;
}
}
}
}
case 11:
{
if (v_a_3086_ == 0)
{
lean_object* v___x_3520_; lean_object* v_canon_3521_; lean_object* v_cache_3522_; lean_object* v___x_3523_; 
v___x_3520_ = lean_st_ref_get(v_a_3088_);
v_canon_3521_ = lean_ctor_get(v___x_3520_, 10);
lean_inc_ref(v_canon_3521_);
lean_dec(v___x_3520_);
v_cache_3522_ = lean_ctor_get(v_canon_3521_, 0);
lean_inc_ref(v_cache_3522_);
lean_dec_ref(v_canon_3521_);
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3522_, v_e_3085_);
lean_dec_ref(v_cache_3522_);
if (lean_obj_tag(v___x_3523_) == 1)
{
lean_object* v_val_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref_known(v_e_3085_, 3);
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
lean_inc_ref(v_e_3085_);
v___x_3532_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3537_ = lean_st_ref_take(v_a_3088_);
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
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3554_, v_e_3085_, v_a_3533_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3559_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_cacheInType_3555_);
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
v___x_3564_ = lean_st_ref_put(v_a_3088_, v___x_3563_);
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
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3532_;
}
}
}
else
{
lean_object* v___x_3573_; lean_object* v_canon_3574_; lean_object* v_cacheInType_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_st_ref_get(v_a_3088_);
v_canon_3574_ = lean_ctor_get(v___x_3573_, 10);
lean_inc_ref(v_canon_3574_);
lean_dec(v___x_3573_);
v_cacheInType_3575_ = lean_ctor_get(v_canon_3574_, 1);
lean_inc_ref(v_cacheInType_3575_);
lean_dec_ref(v_canon_3574_);
v___x_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3575_, v_e_3085_);
lean_dec_ref(v_cacheInType_3575_);
if (lean_obj_tag(v___x_3576_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref_known(v_e_3085_, 3);
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
lean_inc_ref(v_e_3085_);
v___x_3585_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
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
v___x_3590_ = lean_st_ref_take(v_a_3088_);
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
v___x_3612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3608_, v_e_3085_, v_a_3586_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v___x_3612_);
v___x_3614_ = v___x_3610_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_cache_3607_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3612_);
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
v___x_3617_ = lean_st_ref_put(v_a_3088_, v___x_3616_);
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
lean_dec_ref_known(v_e_3085_, 3);
return v___x_3585_;
}
}
}
}
case 10:
{
lean_object* v_data_3626_; lean_object* v_expr_3627_; lean_object* v___x_3628_; 
v_data_3626_ = lean_ctor_get(v_e_3085_, 0);
v_expr_3627_ = lean_ctor_get(v_e_3085_, 1);
lean_inc_ref(v_expr_3627_);
v___x_3628_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3627_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3643_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3643_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3643_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
size_t v___x_3633_; size_t v___x_3634_; uint8_t v___x_3635_; 
v___x_3633_ = lean_ptr_addr(v_expr_3627_);
v___x_3634_ = lean_ptr_addr(v_a_3629_);
v___x_3635_ = lean_usize_dec_eq(v___x_3633_, v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_inc(v_data_3626_);
lean_dec_ref_known(v_e_3085_, 2);
v___x_3636_ = l_Lean_Expr_mdata___override(v_data_3626_, v_a_3629_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3636_);
v___x_3638_ = v___x_3631_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
else
{
lean_object* v___x_3641_; 
lean_dec(v_a_3629_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v_e_3085_);
v___x_3641_ = v___x_3631_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_e_3085_);
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
else
{
lean_dec_ref_known(v_e_3085_, 2);
return v___x_3628_;
}
}
default: 
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_e_3085_);
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3645_, uint8_t v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
if (v_a_3646_ == 0)
{
uint8_t v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = 1;
lean_inc_ref(v_e_3645_);
v___x_3655_ = l_Lean_Meta_isProp(v_e_3645_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; uint8_t v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v___x_3657_ = lean_unbox(v_a_3656_);
lean_dec(v_a_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
v___x_3658_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3645_, v___x_3654_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
return v___x_3659_;
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v_e_3645_);
v_a_3660_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3655_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3655_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3669_, lean_object* v_e_3670_, uint8_t v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
if (lean_obj_tag(v_e_3670_) == 7)
{
lean_object* v_binderName_3679_; lean_object* v_binderType_3680_; lean_object* v_body_3681_; uint8_t v_binderInfo_3682_; lean_object* v___f_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_binderName_3679_ = lean_ctor_get(v_e_3670_, 0);
lean_inc(v_binderName_3679_);
v_binderType_3680_ = lean_ctor_get(v_e_3670_, 1);
lean_inc_ref(v_binderType_3680_);
v_body_3681_ = lean_ctor_get(v_e_3670_, 2);
lean_inc_ref(v_body_3681_);
v_binderInfo_3682_ = lean_ctor_get_uint8(v_e_3670_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3670_, 3);
lean_inc_ref(v_fvars_3669_);
v___f_3683_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3683_, 0, v_fvars_3669_);
lean_closure_set(v___f_3683_, 1, v_body_3681_);
v___x_3684_ = lean_expr_instantiate_rev(v_binderType_3680_, v_fvars_3669_);
lean_dec_ref(v_fvars_3669_);
lean_dec_ref(v_binderType_3680_);
v___x_3685_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3684_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = 0;
v___x_3688_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_binderName_3679_, v_binderInfo_3682_, v_a_3686_, v___f_3683_, v___x_3687_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3688_;
}
else
{
lean_dec_ref(v___f_3683_);
lean_dec(v_binderName_3679_);
return v___x_3685_;
}
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_expr_instantiate_rev(v_e_3670_, v_fvars_3669_);
lean_dec_ref(v_e_3670_);
v___x_3690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3689_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; uint8_t v___x_3692_; uint8_t v___x_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = 0;
v___x_3693_ = 1;
v___x_3694_ = 1;
v___x_3695_ = l_Lean_Meta_mkForallFVars(v_fvars_3669_, v_a_3691_, v___x_3692_, v___x_3693_, v___x_3693_, v___x_3694_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
lean_dec_ref(v_fvars_3669_);
return v___x_3695_;
}
else
{
lean_dec_ref(v_fvars_3669_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3696_, lean_object* v_body_3697_, lean_object* v_x_3698_, uint8_t v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_array_push(v_fvars_3696_, v_x_3698_);
v___x_3708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3707_, v_body_3697_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_){
_start:
{
uint8_t v_a_boxed_3718_; lean_object* v_res_3719_; 
v_a_boxed_3718_ = lean_unbox(v_a_3710_);
v_res_3719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3709_, v_a_boxed_3718_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
uint8_t v_a_boxed_3729_; lean_object* v_res_3730_; 
v_a_boxed_3729_ = lean_unbox(v_a_3721_);
v_res_3730_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3720_, v_a_boxed_3729_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
uint8_t v_a_boxed_3740_; lean_object* v_res_3741_; 
v_a_boxed_3740_ = lean_unbox(v_a_3732_);
v_res_3741_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3731_, v_a_boxed_3740_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
uint8_t v_a_boxed_3751_; lean_object* v_res_3752_; 
v_a_boxed_3751_ = lean_unbox(v_a_3743_);
v_res_3752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3742_, v_a_boxed_3751_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
uint8_t v_a_boxed_3762_; lean_object* v_res_3763_; 
v_a_boxed_3762_ = lean_unbox(v_a_3754_);
v_res_3763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3753_, v_a_boxed_3762_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3764_, lean_object* v_e_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
uint8_t v_a_boxed_3774_; lean_object* v_res_3775_; 
v_a_boxed_3774_ = lean_unbox(v_a_3766_);
v_res_3775_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3764_, v_e_3765_, v_a_boxed_3774_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3776_, lean_object* v_e_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
uint8_t v_a_boxed_3786_; lean_object* v_res_3787_; 
v_a_boxed_3786_ = lean_unbox(v_a_3778_);
v_res_3787_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3776_, v_e_3777_, v_a_boxed_3786_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3788_, lean_object* v_report_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
uint8_t v_report_boxed_3798_; uint8_t v_a_boxed_3799_; lean_object* v_res_3800_; 
v_report_boxed_3798_ = lean_unbox(v_report_3789_);
v_a_boxed_3799_ = lean_unbox(v_a_3790_);
v_res_3800_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3788_, v_report_boxed_3798_, v_a_boxed_3799_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
uint8_t v_a_boxed_3810_; lean_object* v_res_3811_; 
v_a_boxed_3810_ = lean_unbox(v_a_3802_);
v_res_3811_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3801_, v_a_boxed_3810_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3812_, lean_object* v_e_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
uint8_t v_a_boxed_3822_; lean_object* v_res_3823_; 
v_a_boxed_3822_ = lean_unbox(v_a_3814_);
v_res_3823_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3812_, v_e_3813_, v_a_boxed_3822_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3824_, lean_object* v_00_u03b1_3825_, lean_object* v_c_3826_, lean_object* v_a_3827_, lean_object* v_b_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
uint8_t v_a_boxed_3837_; lean_object* v_res_3838_; 
v_a_boxed_3837_ = lean_unbox(v_a_3829_);
v_res_3838_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3824_, v_00_u03b1_3825_, v_c_3826_, v_a_3827_, v_b_3828_, v_a_boxed_3837_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3839_, lean_object* v_00_u03b1_3840_, lean_object* v_c_3841_, lean_object* v_inst_3842_, lean_object* v_a_3843_, lean_object* v_b_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
uint8_t v_a_boxed_3853_; lean_object* v_res_3854_; 
v_a_boxed_3853_ = lean_unbox(v_a_3845_);
v_res_3854_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3839_, v_00_u03b1_3840_, v_c_3841_, v_inst_3842_, v_a_3843_, v_b_3844_, v_a_boxed_3853_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
uint8_t v_a_boxed_3864_; lean_object* v_res_3865_; 
v_a_boxed_3864_ = lean_unbox(v_a_3856_);
v_res_3865_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3855_, v_a_boxed_3864_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
uint8_t v_a_boxed_3875_; lean_object* v_res_3876_; 
v_a_boxed_3875_ = lean_unbox(v_a_3867_);
v_res_3876_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3866_, v_a_boxed_3875_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3877_, lean_object* v_prop_3878_, lean_object* v_inst_3879_, lean_object* v_e_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
uint8_t v_a_boxed_3889_; lean_object* v_res_3890_; 
v_a_boxed_3889_ = lean_unbox(v_a_3881_);
v_res_3890_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3877_, v_prop_3878_, v_inst_3879_, v_e_3880_, v_a_boxed_3889_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
lean_dec(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3891_, lean_object* v_report_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
uint8_t v_report_boxed_3901_; uint8_t v_a_boxed_3902_; lean_object* v_res_3903_; 
v_report_boxed_3901_ = lean_unbox(v_report_3892_);
v_a_boxed_3902_ = lean_unbox(v_a_3893_);
v_res_3903_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3891_, v_report_boxed_3901_, v_a_boxed_3902_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3904_, lean_object* v_prop_3905_, lean_object* v_h_3906_, lean_object* v_e_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
uint8_t v_a_boxed_3916_; lean_object* v_res_3917_; 
v_a_boxed_3916_ = lean_unbox(v_a_3908_);
v_res_3917_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3904_, v_prop_3905_, v_h_3906_, v_e_3907_, v_a_boxed_3916_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
uint8_t v_a_boxed_3927_; lean_object* v_res_3928_; 
v_a_boxed_3927_ = lean_unbox(v_a_3919_);
v_res_3928_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3918_, v_a_boxed_3927_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_3929_, lean_object* v___x_3930_, lean_object* v_a_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
uint8_t v___y_62685__boxed_3941_; lean_object* v_res_3942_; 
v___y_62685__boxed_3941_ = lean_unbox(v___y_3933_);
v_res_3942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_3929_, v___x_3930_, v_a_3931_, v_b_3932_, v___y_62685__boxed_3941_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v___x_3930_);
lean_dec(v_upperBound_3929_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object* v___x_3943_, lean_object* v_snd_3944_, lean_object* v_a_3945_, lean_object* v___x_3946_, lean_object* v_fst_3947_, lean_object* v___x_3948_, lean_object* v_____r_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v___x_62749__boxed_3958_; uint8_t v___y_62752__boxed_3959_; lean_object* v_res_3960_; 
v___x_62749__boxed_3958_ = lean_unbox(v___x_3946_);
v___y_62752__boxed_3959_ = lean_unbox(v___y_3950_);
v_res_3960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_3943_, v_snd_3944_, v_a_3945_, v___x_62749__boxed_3958_, v_fst_3947_, v___x_3948_, v_____r_3949_, v___y_62752__boxed_3959_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec_ref(v___x_3948_);
lean_dec(v_a_3945_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
uint8_t v_a_boxed_3970_; lean_object* v_res_3971_; 
v_a_boxed_3970_ = lean_unbox(v_a_3962_);
v_res_3971_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_3961_, v_a_boxed_3970_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3972_, lean_object* v_prop_3973_, lean_object* v_h_3974_, lean_object* v_e_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
uint8_t v_a_boxed_3984_; lean_object* v_res_3985_; 
v_a_boxed_3984_ = lean_unbox(v_a_3976_);
v_res_3985_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3972_, v_prop_3973_, v_h_3974_, v_e_3975_, v_a_boxed_3984_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v___y_62929__boxed_3998_; lean_object* v_res_3999_; 
v___y_62929__boxed_3998_ = lean_unbox(v___y_3990_);
v_res_3999_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_3986_, v_x_3987_, v_x_3988_, v_x_3989_, v___y_62929__boxed_3998_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
uint8_t v_a_boxed_4009_; lean_object* v_res_4010_; 
v_a_boxed_4009_ = lean_unbox(v_a_4001_);
v_res_4010_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4000_, v_a_boxed_4009_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_4011_, uint8_t v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_4011_, v___y_4018_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
uint8_t v___y_65460__boxed_4030_; lean_object* v_res_4031_; 
v___y_65460__boxed_4030_ = lean_unbox(v___y_4022_);
v_res_4031_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4021_, v___y_65460__boxed_4030_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_4032_, uint8_t v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_4032_, v___y_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
uint8_t v___y_65486__boxed_4051_; lean_object* v_res_4052_; 
v___y_65486__boxed_4051_ = lean_unbox(v___y_4043_);
v_res_4052_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4042_, v___y_65486__boxed_4051_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(lean_object* v_00_u03b1_4053_, lean_object* v_name_4054_, lean_object* v_type_4055_, lean_object* v_val_4056_, lean_object* v_k_4057_, uint8_t v_nondep_4058_, uint8_t v_kind_4059_, uint8_t v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___redArg(v_name_4054_, v_type_4055_, v_val_4056_, v_k_4057_, v_nondep_4058_, v_kind_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25___boxed(lean_object* v_00_u03b1_4069_, lean_object* v_name_4070_, lean_object* v_type_4071_, lean_object* v_val_4072_, lean_object* v_k_4073_, lean_object* v_nondep_4074_, lean_object* v_kind_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v_nondep_boxed_4084_; uint8_t v_kind_boxed_4085_; uint8_t v___y_65512__boxed_4086_; lean_object* v_res_4087_; 
v_nondep_boxed_4084_ = lean_unbox(v_nondep_4074_);
v_kind_boxed_4085_ = lean_unbox(v_kind_4075_);
v___y_65512__boxed_4086_ = lean_unbox(v___y_4076_);
v_res_4087_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__25(v_00_u03b1_4069_, v_name_4070_, v_type_4071_, v_val_4072_, v_k_4073_, v_nondep_boxed_4084_, v_kind_boxed_4085_, v___y_65512__boxed_4086_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(lean_object* v_00_u03b1_4088_, lean_object* v_name_4089_, uint8_t v_bi_4090_, lean_object* v_type_4091_, lean_object* v_k_4092_, uint8_t v_kind_4093_, uint8_t v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___redArg(v_name_4089_, v_bi_4090_, v_type_4091_, v_k_4092_, v_kind_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_name_4104_, lean_object* v_bi_4105_, lean_object* v_type_4106_, lean_object* v_k_4107_, lean_object* v_kind_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v_bi_boxed_4117_; uint8_t v_kind_boxed_4118_; uint8_t v___y_65538__boxed_4119_; lean_object* v_res_4120_; 
v_bi_boxed_4117_ = lean_unbox(v_bi_4105_);
v_kind_boxed_4118_ = lean_unbox(v_kind_4108_);
v___y_65538__boxed_4119_ = lean_unbox(v___y_4109_);
v_res_4120_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__28(v_00_u03b1_4103_, v_name_4104_, v_bi_boxed_4117_, v_type_4106_, v_k_4107_, v_kind_boxed_4118_, v___y_65538__boxed_4119_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4121_, lean_object* v_m_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4122_, v_a_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4125_, lean_object* v_m_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4125_, v_m_4126_, v_a_4127_);
lean_dec_ref(v_a_4127_);
lean_dec_ref(v_m_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4129_, lean_object* v_m_4130_, lean_object* v_a_4131_, lean_object* v_b_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4130_, v_a_4131_, v_b_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4134_, lean_object* v_msg_4135_, uint8_t v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4134_, v_msg_4135_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4145_, lean_object* v_msg_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
uint8_t v___y_65568__boxed_4155_; lean_object* v_res_4156_; 
v___y_65568__boxed_4155_ = lean_unbox(v___y_4147_);
v_res_4156_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4145_, v_msg_4146_, v___y_65568__boxed_4155_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4157_, lean_object* v___x_4158_, lean_object* v___x_4159_, lean_object* v_inst_4160_, lean_object* v_R_4161_, lean_object* v_a_4162_, lean_object* v_b_4163_, lean_object* v_c_4164_, uint8_t v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4157_, v___x_4159_, v_a_4162_, v_b_4163_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object* v_upperBound_4174_, lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v_inst_4177_, lean_object* v_R_4178_, lean_object* v_a_4179_, lean_object* v_b_4180_, lean_object* v_c_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
uint8_t v___y_65598__boxed_4190_; lean_object* v_res_4191_; 
v___y_65598__boxed_4190_ = lean_unbox(v___y_4182_);
v_res_4191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4174_, v___x_4175_, v___x_4176_, v_inst_4177_, v_R_4178_, v_a_4179_, v_b_4180_, v_c_4181_, v___y_65598__boxed_4190_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec_ref(v___x_4176_);
lean_dec(v___x_4175_);
lean_dec(v_upperBound_4174_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_4192_, lean_object* v_a_4193_, lean_object* v_x_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_4193_, v_x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_4196_, lean_object* v_a_4197_, lean_object* v_x_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_4196_, v_a_4197_, v_x_4198_);
lean_dec(v_x_4198_);
lean_dec_ref(v_a_4197_);
return v_res_4199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_4200_, lean_object* v_a_4201_, lean_object* v_x_4202_){
_start:
{
uint8_t v___x_4203_; 
v___x_4203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_4201_, v_x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4204_, lean_object* v_a_4205_, lean_object* v_x_4206_){
_start:
{
uint8_t v_res_4207_; lean_object* v_r_4208_; 
v_res_4207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_4204_, v_a_4205_, v_x_4206_);
lean_dec(v_x_4206_);
lean_dec_ref(v_a_4205_);
v_r_4208_ = lean_box(v_res_4207_);
return v_r_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4209_, lean_object* v_data_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4212_, lean_object* v_a_4213_, lean_object* v_b_4214_, lean_object* v_x_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_4213_, v_b_4214_, v_x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29(lean_object* v_00_u03b2_4217_, lean_object* v_i_4218_, lean_object* v_source_4219_, lean_object* v_target_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29___redArg(v_i_4218_, v_source_4219_, v_target_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34(lean_object* v_00_u03b2_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__29_spec__34___redArg(v_x_4223_, v_x_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4226_, lean_object* v_i_4227_, lean_object* v_arg_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4226_, v_i_4227_, v_arg_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4250_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4250_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4250_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
uint8_t v___x_4239_; 
v___x_4239_ = lean_unbox(v_a_4235_);
lean_dec(v_a_4235_);
if (v___x_4239_ == 3)
{
uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4240_ = 0;
v___x_4241_ = lean_box(v___x_4240_);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 0, v___x_4241_);
v___x_4243_ = v___x_4237_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
else
{
uint8_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4245_ = 1;
v___x_4246_ = lean_box(v___x_4245_);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 0, v___x_4246_);
v___x_4248_ = v___x_4237_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4234_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4234_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4259_, lean_object* v_i_4260_, lean_object* v_arg_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4259_, v_i_4260_, v_arg_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_i_4260_);
lean_dec_ref(v_pinfos_4259_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4268_, lean_object* v_opts_4269_, lean_object* v_act_4270_, lean_object* v_decl_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
lean_inc(v___y_4275_);
lean_inc_ref(v___y_4274_);
lean_inc(v___y_4273_);
lean_inc_ref(v___y_4272_);
v___x_4279_ = lean_apply_6(v_act_4270_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
v___x_4280_ = l_Lean_profileitIOUnsafe___redArg(v_category_4268_, v_opts_4269_, v___x_4279_, v_decl_4271_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4281_, lean_object* v_opts_4282_, lean_object* v_act_4283_, lean_object* v_decl_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4281_, v_opts_4282_, v_act_4283_, v_decl_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec_ref(v_opts_4282_);
lean_dec_ref(v_category_4281_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4293_, lean_object* v_category_4294_, lean_object* v_opts_4295_, lean_object* v_act_4296_, lean_object* v_decl_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4294_, v_opts_4295_, v_act_4296_, v_decl_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4306_, lean_object* v_category_4307_, lean_object* v_opts_4308_, lean_object* v_act_4309_, lean_object* v_decl_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4306_, v_category_4307_, v_opts_4308_, v_act_4309_, v_decl_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_opts_4308_);
lean_dec_ref(v_category_4307_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4319_, lean_object* v_e_4320_, uint8_t v___x_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___y_4330_; lean_object* v___x_4339_; uint8_t v_transparency_4340_; uint8_t v___x_4341_; 
v___x_4339_ = l_Lean_Meta_Context_config(v___y_4324_);
v_transparency_4340_ = lean_ctor_get_uint8(v___x_4339_, 9);
lean_dec_ref(v___x_4339_);
v___x_4341_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4340_, v___x_4319_);
if (v___x_4341_ == 0)
{
lean_object* v_keyedConfig_4342_; uint8_t v_trackZetaDelta_4343_; lean_object* v_zetaDeltaSet_4344_; lean_object* v_lctx_4345_; lean_object* v_localInstances_4346_; lean_object* v_defEqCtx_x3f_4347_; lean_object* v_synthPendingDepth_4348_; lean_object* v_customCanUnfoldPredicate_x3f_4349_; uint8_t v_univApprox_4350_; uint8_t v_inTypeClassResolution_4351_; uint8_t v_cacheInferType_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_keyedConfig_4342_ = lean_ctor_get(v___y_4324_, 0);
v_trackZetaDelta_4343_ = lean_ctor_get_uint8(v___y_4324_, sizeof(void*)*7);
v_zetaDeltaSet_4344_ = lean_ctor_get(v___y_4324_, 1);
v_lctx_4345_ = lean_ctor_get(v___y_4324_, 2);
v_localInstances_4346_ = lean_ctor_get(v___y_4324_, 3);
v_defEqCtx_x3f_4347_ = lean_ctor_get(v___y_4324_, 4);
v_synthPendingDepth_4348_ = lean_ctor_get(v___y_4324_, 5);
v_customCanUnfoldPredicate_x3f_4349_ = lean_ctor_get(v___y_4324_, 6);
v_univApprox_4350_ = lean_ctor_get_uint8(v___y_4324_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4351_ = lean_ctor_get_uint8(v___y_4324_, sizeof(void*)*7 + 2);
v_cacheInferType_4352_ = lean_ctor_get_uint8(v___y_4324_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4342_);
v___x_4353_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4319_, v_keyedConfig_4342_);
lean_inc(v_customCanUnfoldPredicate_x3f_4349_);
lean_inc(v_synthPendingDepth_4348_);
lean_inc(v_defEqCtx_x3f_4347_);
lean_inc_ref(v_localInstances_4346_);
lean_inc_ref(v_lctx_4345_);
lean_inc(v_zetaDeltaSet_4344_);
v___x_4354_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
lean_ctor_set(v___x_4354_, 1, v_zetaDeltaSet_4344_);
lean_ctor_set(v___x_4354_, 2, v_lctx_4345_);
lean_ctor_set(v___x_4354_, 3, v_localInstances_4346_);
lean_ctor_set(v___x_4354_, 4, v_defEqCtx_x3f_4347_);
lean_ctor_set(v___x_4354_, 5, v_synthPendingDepth_4348_);
lean_ctor_set(v___x_4354_, 6, v_customCanUnfoldPredicate_x3f_4349_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*7, v_trackZetaDelta_4343_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*7 + 1, v_univApprox_4350_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4351_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*7 + 3, v_cacheInferType_4352_);
v___x_4355_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4320_, v___x_4321_, v___y_4322_, v___y_4323_, v___x_4354_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec_ref_known(v___x_4354_, 7);
v___y_4330_ = v___x_4355_;
goto v___jp_4329_;
}
else
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4320_, v___x_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
v___y_4330_ = v___x_4356_;
goto v___jp_4329_;
}
v___jp_4329_:
{
if (lean_obj_tag(v___y_4330_) == 0)
{
return v___y_4330_;
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
v_a_4331_ = lean_ctor_get(v___y_4330_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___y_4330_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___y_4330_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___y_4330_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4357_, lean_object* v_e_4358_, lean_object* v___x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
uint8_t v___x_2117__boxed_4367_; uint8_t v___x_2118__boxed_4368_; lean_object* v_res_4369_; 
v___x_2117__boxed_4367_ = lean_unbox(v___x_4357_);
v___x_2118__boxed_4368_ = lean_unbox(v___x_4359_);
v_res_4369_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2117__boxed_4367_, v_e_4358_, v___x_2118__boxed_4368_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; uint8_t v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___f_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4376_);
v___x_4380_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4381_ = 0;
v___x_4382_ = 2;
v___x_4383_ = lean_box(v___x_4382_);
v___x_4384_ = lean_box(v___x_4381_);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4385_, 0, v___x_4383_);
lean_closure_set(v___f_4385_, 1, v_e_4371_);
lean_closure_set(v___f_4385_, 2, v___x_4384_);
v___x_4386_ = lean_box(0);
v___x_4387_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4380_, v___x_4379_, v___f_4385_, v___x_4386_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec_ref(v___x_4379_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Meta_Sym_canon(v_e_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
return v_res_4396_;
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

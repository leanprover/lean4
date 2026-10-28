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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
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
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nfailed to synthesize"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1_value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f(lean_object* v_e_89_){
_start:
{
lean_object* v_e_91_; lean_object* v___x_107_; 
v___x_107_ = l_Lean_Expr_consumeMData(v_e_89_);
lean_dec_ref(v_e_89_);
if (lean_obj_tag(v___x_107_) == 9)
{
lean_object* v_a_108_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_a_108_);
if (lean_obj_tag(v_a_108_) == 0)
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref_known(v___x_107_, 1);
v_val_109_ = lean_ctor_get(v_a_108_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_108_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v_a_108_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v_a_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set_tag(v___x_111_, 1);
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_val_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
else
{
lean_dec_ref(v_a_108_);
v_e_91_ = v___x_107_;
goto v___jp_90_;
}
}
else
{
v_e_91_ = v___x_107_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = l_Lean_Expr_cleanupAnnotations(v_e_91_);
lean_dec_ref(v_e_91_);
v___x_93_ = l_Lean_Expr_isApp(v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_92_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_92_);
lean_dec_ref(v___x_92_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_95_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_98_);
lean_dec_ref(v___x_95_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
lean_dec_ref(v___x_98_);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v___x_103_ = l_Lean_Expr_isConstOf(v___x_101_, v___x_102_);
lean_dec_ref(v___x_101_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_95_);
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v_arg_105_; 
v_arg_105_ = lean_ctor_get(v___x_95_, 1);
lean_inc_ref(v_arg_105_);
lean_dec_ref(v___x_95_);
v_e_89_ = v_arg_105_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg(lean_object* v_args_123_, lean_object* v_a_124_){
_start:
{
uint8_t v___y_130_; lean_object* v___y_131_; uint8_t v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v_args_165_; uint8_t v_modified_166_; lean_object* v___y_167_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v_modified_197_; 
v___x_195_ = lean_array_get_size(v_args_123_);
v___x_196_ = lean_unsigned_to_nat(3u);
v_modified_197_ = lean_nat_dec_eq(v___x_195_, v___x_196_);
if (v_modified_197_ == 0)
{
lean_dec_ref(v_args_123_);
goto v___jp_126_;
}
else
{
uint8_t v_modified_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_modified_198_ = 0;
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_array_fget_borrowed(v_args_123_, v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v___x_202_ = l_Lean_Expr_isAppOf(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
v_args_165_ = v_args_123_;
v_modified_166_ = v_modified_198_;
v___y_167_ = v_a_124_;
goto v___jp_164_;
}
else
{
lean_object* v___x_203_; 
lean_inc(v___x_200_);
v___x_203_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f(v___x_200_);
if (lean_obj_tag(v___x_203_) == 1)
{
lean_object* v_val_204_; lean_object* v___x_205_; lean_object* v_args_206_; 
v_val_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_203_, 1);
v___x_205_ = l_Lean_mkRawNatLit(v_val_204_);
v_args_206_ = lean_array_fset(v_args_123_, v___x_199_, v___x_205_);
v_args_165_ = v_args_206_;
v_modified_166_ = v_modified_197_;
v___y_167_ = v_a_124_;
goto v___jp_164_;
}
else
{
lean_dec(v___x_203_);
v_args_165_ = v_args_123_;
v_modified_166_ = v_modified_198_;
v___y_167_ = v_a_124_;
goto v___jp_164_;
}
}
}
v___jp_126_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
lean_dec_ref(v___y_131_);
goto v___jp_126_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___y_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
v___jp_134_:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_136_, v___y_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_155_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_155_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_155_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_155_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
uint8_t v___x_144_; 
v___x_144_ = lean_unbox(v_a_140_);
lean_dec(v_a_140_);
if (v___x_144_ == 0)
{
lean_del_object(v___x_142_);
v___y_130_ = v___y_135_;
v___y_131_ = v___y_137_;
goto v___jp_129_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_array_fget_borrowed(v___y_137_, v___x_145_);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__1));
v___x_148_ = l_Lean_Expr_isConstOf(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_149_ = l_Lean_Int_mkType;
v___x_150_ = lean_array_fset(v___y_137_, v___x_145_, v___x_149_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_151_);
v___x_153_ = v___x_142_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
else
{
lean_del_object(v___x_142_);
v___y_130_ = v___y_135_;
v___y_131_ = v___y_137_;
goto v___jp_129_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v___y_137_);
v_a_156_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_139_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_139_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
v___jp_164_:
{
lean_object* v___x_168_; lean_object* v_inst_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(2u);
v_inst_169_ = lean_array_fget_borrowed(v_args_165_, v___x_168_);
lean_inc(v_inst_169_);
v___x_170_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_169_, v___y_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_186_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_186_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_186_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_186_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_unbox(v_a_171_);
lean_dec(v_a_171_);
if (v___x_175_ == 0)
{
lean_inc(v_inst_169_);
lean_del_object(v___x_173_);
v___y_135_ = v_modified_166_;
v___y_136_ = v_inst_169_;
v___y_137_ = v_args_165_;
v___y_138_ = v___y_167_;
goto v___jp_134_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_array_fget_borrowed(v_args_165_, v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__3));
v___x_179_ = l_Lean_Expr_isConstOf(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_180_ = l_Lean_Nat_mkType;
v___x_181_ = lean_array_fset(v_args_165_, v___x_176_, v___x_180_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_182_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_inc(v_inst_169_);
lean_del_object(v___x_173_);
v___y_135_ = v_modified_166_;
v___y_136_ = v_inst_169_;
v___y_137_ = v_args_165_;
v___y_138_ = v___y_167_;
goto v___jp_134_;
}
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec_ref(v_args_165_);
v_a_187_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_170_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_170_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___boxed(lean_object* v_args_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg(v_args_207_, v_a_208_);
lean_dec(v_a_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(lean_object* v_args_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg(v_args_211_, v_a_213_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(lean_object* v_args_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_args_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__1));
v___x_230_ = l_Lean_mkConst(v___x_229_, v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(lean_object* v_e_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_getBitVecValue_x3f(v_e_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_276_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_276_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_276_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_276_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
if (lean_obj_tag(v_a_238_) == 1)
{
lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_271_; 
lean_del_object(v___x_240_);
v_val_242_ = lean_ctor_get(v_a_238_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_271_ == 0)
{
v___x_244_ = v_a_238_;
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v_a_238_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_fst_246_ = lean_ctor_get(v_val_242_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_val_242_, 1);
lean_inc(v_snd_247_);
lean_dec(v_val_242_);
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2);
v___x_249_ = l_Lean_mkNatLit(v_fst_246_);
v___x_250_ = l_Lean_Expr_app___override(v___x_248_, v___x_249_);
v___x_251_ = l_Lean_Meta_mkNumeral(v___x_250_, v_snd_247_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v_a_252_);
v___x_257_ = v___x_244_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
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
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_del_object(v___x_244_);
v_a_263_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_251_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_251_);
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
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec(v_a_238_);
v___x_272_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_272_);
v___x_274_ = v___x_240_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_237_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_237_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___boxed(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__7));
v___x_311_ = l_Lean_mkConst(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_box(0);
v___x_313_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_314_ = l_Lean_mkConst(v___x_313_, v___x_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_324_; 
lean_inc_ref(v_e_315_);
v___x_324_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_315_, v_a_317_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_579_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_579_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_579_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_579_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = l_Lean_Expr_cleanupAnnotations(v_a_325_);
lean_dec(v_a_325_);
v___x_330_ = l_Lean_Expr_isApp(v___x_329_);
if (v___x_330_ == 0)
{
lean_dec_ref(v___x_329_);
lean_del_object(v___x_327_);
lean_dec_ref(v_e_315_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_arg_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc_ref(v_arg_331_);
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_329_);
lean_dec_ref(v___x_329_);
v___x_333_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
lean_del_object(v___x_327_);
v___x_335_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_e_315_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_arg_336_ = lean_ctor_get(v___x_332_, 1);
lean_inc_ref(v_arg_336_);
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
lean_dec_ref(v___x_332_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_340_ == 0)
{
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_e_315_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_arg_341_ = lean_ctor_get(v___x_337_, 1);
lean_inc_ref(v_arg_341_);
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
lean_dec_ref(v___x_337_);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
lean_dec_ref(v_arg_336_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_331_);
v___x_347_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_347_);
lean_dec_ref(v___x_342_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_e_315_);
goto v___jp_321_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec_ref(v___x_342_);
lean_dec_ref(v_e_315_);
v___x_350_ = l_Lean_Meta_getNatValue_x3f(v_arg_341_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec_ref(v_arg_341_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_413_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_413_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_413_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_413_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
if (lean_obj_tag(v_a_351_) == 1)
{
lean_object* v_val_355_; lean_object* v___x_356_; 
lean_del_object(v___x_353_);
v_val_355_ = lean_ctor_get(v_a_351_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v_a_351_, 1);
v___x_356_ = l_Lean_Meta_getNatValue_x3f(v_arg_331_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec_ref(v_arg_331_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_400_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_400_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_400_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_400_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_395_; 
v_val_361_ = lean_ctor_get(v_a_357_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_a_357_);
if (v_isSharedCheck_395_ == 0)
{
v___x_363_ = v_a_357_;
v_isShared_364_ = v_isSharedCheck_395_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v_a_357_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_395_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_nat_dec_eq(v_val_355_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_del_object(v___x_359_);
v___x_367_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__8);
lean_inc(v_val_355_);
v___x_368_ = l_Lean_mkNatLit(v_val_355_);
v___x_369_ = l_Lean_Expr_app___override(v___x_367_, v___x_368_);
v___x_370_ = lean_nat_mod(v_val_361_, v_val_355_);
lean_dec(v_val_355_);
lean_dec(v_val_361_);
v___x_371_ = l_Lean_Meta_mkNumeral(v___x_369_, v___x_370_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_382_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_382_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_a_372_);
v___x_377_ = v___x_363_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
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
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_363_);
v_a_383_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_371_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_371_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_393_; 
lean_del_object(v___x_363_);
lean_dec(v_val_361_);
lean_dec(v_val_355_);
v___x_391_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_391_);
v___x_393_ = v___x_359_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_dec(v_a_357_);
lean_dec(v_val_355_);
v___x_396_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_396_);
v___x_398_ = v___x_359_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_val_355_);
v_a_401_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_356_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_356_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v_a_351_);
lean_dec_ref(v_arg_331_);
v___x_409_ = lean_box(0);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_409_);
v___x_411_ = v___x_353_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_arg_331_);
v_a_414_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_350_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_350_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v___x_342_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_e_315_);
lean_inc_ref(v_arg_341_);
v___x_422_ = l_Lean_Meta_getLitValueModulus_x3f(v_arg_341_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_484_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_484_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_484_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_484_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
if (lean_obj_tag(v_a_423_) == 1)
{
lean_object* v_val_427_; lean_object* v___x_428_; 
v_val_427_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_a_423_, 1);
v___x_428_ = l_Lean_Meta_getNatValue_x3f(v_arg_336_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec_ref(v_arg_336_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_471_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_471_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_471_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_471_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_466_; 
lean_del_object(v___x_425_);
v_val_438_ = lean_ctor_get(v_a_429_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_466_ == 0)
{
v___x_440_ = v_a_429_;
v_isShared_441_ = v_isSharedCheck_466_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_val_438_);
lean_dec(v_a_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_466_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_nat_dec_eq(v_val_427_, v___x_442_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_lt(v_val_438_, v_val_427_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_del_object(v___x_431_);
v___x_445_ = lean_nat_mod(v_val_438_, v_val_427_);
lean_dec(v_val_427_);
lean_dec(v_val_438_);
v___x_446_ = l_Lean_Meta_mkNumeral(v_arg_341_, v___x_445_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_457_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_a_447_);
v___x_452_ = v___x_440_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_del_object(v___x_440_);
v_a_458_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_446_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_446_);
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
else
{
lean_del_object(v___x_440_);
lean_dec(v_val_438_);
lean_dec(v_val_427_);
lean_dec_ref(v_arg_341_);
goto v___jp_433_;
}
}
else
{
lean_del_object(v___x_440_);
lean_dec(v_val_438_);
lean_dec(v_val_427_);
lean_dec_ref(v_arg_341_);
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_del_object(v___x_431_);
lean_dec(v_a_429_);
lean_dec(v_val_427_);
lean_dec_ref(v_arg_341_);
v___x_467_ = lean_box(0);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_467_);
v___x_469_ = v___x_425_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
v___jp_433_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_box(0);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_434_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
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
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_val_427_);
lean_del_object(v___x_425_);
lean_dec_ref(v_arg_341_);
v_a_472_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_428_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_428_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_a_423_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_336_);
v___x_480_ = lean_box(0);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_480_);
v___x_482_ = v___x_425_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_336_);
v_a_485_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_422_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_422_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
else
{
lean_object* v___x_493_; 
lean_dec_ref(v___x_337_);
v___x_493_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm(v_e_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
if (lean_obj_tag(v_a_494_) == 1)
{
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_331_);
return v___x_493_;
}
else
{
lean_object* v___x_495_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = l_Lean_Meta_getNatValue_x3f(v_arg_331_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec_ref(v_arg_331_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_531_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_531_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_531_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_531_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
if (lean_obj_tag(v_a_496_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_498_);
v_val_500_ = lean_ctor_get(v_a_496_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_526_ == 0)
{
v___x_502_ = v_a_496_;
v_isShared_503_ = v_isSharedCheck_526_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v_a_496_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_526_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normNumLit_x3f_bitVecOfNatForm___closed__2);
v___x_505_ = l_Lean_Expr_app___override(v___x_504_, v_arg_336_);
v___x_506_ = l_Lean_Meta_mkNumeral(v___x_505_, v_val_500_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_517_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_a_507_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_512_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_502_);
v_a_518_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_506_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_506_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_a_496_);
lean_dec_ref(v_arg_336_);
v___x_527_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_527_);
v___x_529_ = v___x_498_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_arg_336_);
v_a_532_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_495_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_495_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
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
}
else
{
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_331_);
return v___x_493_;
}
}
}
}
else
{
uint8_t v___x_540_; 
lean_dec_ref(v___x_332_);
v___x_540_ = l_Lean_Expr_isCharLit(v_e_315_);
lean_dec_ref(v_e_315_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_del_object(v___x_327_);
v___x_541_ = l_Lean_Meta_getNatValue_x3f(v_arg_331_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec_ref(v_arg_331_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_566_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_566_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_566_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_566_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
if (lean_obj_tag(v_a_542_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_561_; 
v_val_546_ = lean_ctor_get(v_a_542_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_542_);
if (v_isSharedCheck_561_ == 0)
{
v___x_548_ = v_a_542_;
v_isShared_549_ = v_isSharedCheck_561_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_dec(v_a_542_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_561_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint32_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_550_ = l_Char_ofNat(v_val_546_);
lean_dec(v_val_546_);
v___x_551_ = lean_obj_once(&l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9, &l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9_once, _init_l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__9);
v___x_552_ = lean_uint32_to_nat(v___x_550_);
v___x_553_ = l_Lean_mkRawNatLit(v___x_552_);
v___x_554_ = l_Lean_Expr_app___override(v___x_551_, v___x_553_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_556_);
v___x_558_ = v___x_544_;
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
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec(v_a_542_);
v___x_562_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_562_);
v___x_564_ = v___x_544_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_541_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_541_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_dec_ref(v_arg_331_);
v___x_575_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_575_);
v___x_577_ = v___x_327_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_e_315_);
v_a_580_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_324_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_324_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f___boxed(lean_object* v_e_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_597_, lean_object* v_k_598_, uint8_t v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_608_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
if (v_a_599_ == 0)
{
lean_object* v___x_609_; lean_object* v_canon_610_; lean_object* v_cache_611_; lean_object* v___x_612_; 
v___x_609_ = lean_st_ref_get(v_a_601_);
v_canon_610_ = lean_ctor_get(v___x_609_, 10);
lean_inc_ref(v_canon_610_);
lean_dec(v___x_609_);
v_cache_611_ = lean_ctor_get(v_canon_610_, 0);
lean_inc_ref(v_cache_611_);
lean_dec_ref(v_canon_610_);
lean_inc_ref(v_e_597_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_607_, v___x_608_, v_cache_611_, v_e_597_);
lean_dec_ref(v_cache_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v_k_598_);
lean_dec_ref(v_e_597_);
v_val_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 0);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_val_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_612_);
v___x_621_ = lean_box(v_a_599_);
lean_inc(v_a_605_);
lean_inc_ref(v_a_604_);
lean_inc(v_a_603_);
lean_inc_ref(v_a_602_);
lean_inc(v_a_601_);
lean_inc_ref(v_a_600_);
v___x_622_ = lean_apply_8(v_k_598_, v___x_621_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, lean_box(0));
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_662_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_662_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_662_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_662_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v_canon_628_; lean_object* v_share_629_; lean_object* v_maxFVar_630_; lean_object* v_proofInstInfo_631_; lean_object* v_proofInstInfoFVar_632_; lean_object* v_inferType_633_; lean_object* v_getLevel_634_; lean_object* v_congrInfo_635_; lean_object* v_defEqI_636_; lean_object* v_extensions_637_; lean_object* v_issues_638_; lean_object* v_instanceOverrides_639_; uint8_t v_debug_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_661_; 
v___x_627_ = lean_st_ref_take(v_a_601_);
v_canon_628_ = lean_ctor_get(v___x_627_, 10);
v_share_629_ = lean_ctor_get(v___x_627_, 0);
v_maxFVar_630_ = lean_ctor_get(v___x_627_, 1);
v_proofInstInfo_631_ = lean_ctor_get(v___x_627_, 2);
v_proofInstInfoFVar_632_ = lean_ctor_get(v___x_627_, 3);
v_inferType_633_ = lean_ctor_get(v___x_627_, 4);
v_getLevel_634_ = lean_ctor_get(v___x_627_, 5);
v_congrInfo_635_ = lean_ctor_get(v___x_627_, 6);
v_defEqI_636_ = lean_ctor_get(v___x_627_, 7);
v_extensions_637_ = lean_ctor_get(v___x_627_, 8);
v_issues_638_ = lean_ctor_get(v___x_627_, 9);
v_instanceOverrides_639_ = lean_ctor_get(v___x_627_, 11);
v_debug_640_ = lean_ctor_get_uint8(v___x_627_, sizeof(void*)*12);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_661_ == 0)
{
v___x_642_ = v___x_627_;
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_instanceOverrides_639_);
lean_inc(v_canon_628_);
lean_inc(v_issues_638_);
lean_inc(v_extensions_637_);
lean_inc(v_defEqI_636_);
lean_inc(v_congrInfo_635_);
lean_inc(v_getLevel_634_);
lean_inc(v_inferType_633_);
lean_inc(v_proofInstInfoFVar_632_);
lean_inc(v_proofInstInfo_631_);
lean_inc(v_maxFVar_630_);
lean_inc(v_share_629_);
lean_dec(v___x_627_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_cache_644_; lean_object* v_cacheInType_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_660_; 
v_cache_644_ = lean_ctor_get(v_canon_628_, 0);
v_cacheInType_645_ = lean_ctor_get(v_canon_628_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_canon_628_);
if (v_isSharedCheck_660_ == 0)
{
v___x_647_ = v_canon_628_;
v_isShared_648_ = v_isSharedCheck_660_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_cacheInType_645_);
lean_inc(v_cache_644_);
lean_dec(v_canon_628_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_660_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_inc(v_a_623_);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_607_, v___x_608_, v_cache_644_, v_e_597_, v_a_623_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_cacheInType_645_);
v___x_651_ = v_reuseFailAlloc_659_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 10, v___x_651_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_share_629_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_maxFVar_630_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_proofInstInfo_631_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_proofInstInfoFVar_632_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_inferType_633_);
lean_ctor_set(v_reuseFailAlloc_658_, 5, v_getLevel_634_);
lean_ctor_set(v_reuseFailAlloc_658_, 6, v_congrInfo_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 7, v_defEqI_636_);
lean_ctor_set(v_reuseFailAlloc_658_, 8, v_extensions_637_);
lean_ctor_set(v_reuseFailAlloc_658_, 9, v_issues_638_);
lean_ctor_set(v_reuseFailAlloc_658_, 10, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 11, v_instanceOverrides_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_658_, sizeof(void*)*12, v_debug_640_);
v___x_653_ = v_reuseFailAlloc_658_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_st_ref_put(v_a_601_, v___x_653_);
if (v_isShared_626_ == 0)
{
v___x_656_ = v___x_625_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_623_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_597_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v_canon_664_; lean_object* v_cacheInType_665_; lean_object* v___x_666_; 
v___x_663_ = lean_st_ref_get(v_a_601_);
v_canon_664_ = lean_ctor_get(v___x_663_, 10);
lean_inc_ref(v_canon_664_);
lean_dec(v___x_663_);
v_cacheInType_665_ = lean_ctor_get(v_canon_664_, 1);
lean_inc_ref(v_cacheInType_665_);
lean_dec_ref(v_canon_664_);
lean_inc_ref(v_e_597_);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_607_, v___x_608_, v_cacheInType_665_, v_e_597_);
lean_dec_ref(v_cacheInType_665_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_k_598_);
lean_dec_ref(v_e_597_);
v_val_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 0);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_666_);
v___x_675_ = lean_box(v_a_599_);
lean_inc(v_a_605_);
lean_inc_ref(v_a_604_);
lean_inc(v_a_603_);
lean_inc_ref(v_a_602_);
lean_inc(v_a_601_);
lean_inc_ref(v_a_600_);
v___x_676_ = lean_apply_8(v_k_598_, v___x_675_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, lean_box(0));
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_716_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_716_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_716_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_716_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v_canon_682_; lean_object* v_share_683_; lean_object* v_maxFVar_684_; lean_object* v_proofInstInfo_685_; lean_object* v_proofInstInfoFVar_686_; lean_object* v_inferType_687_; lean_object* v_getLevel_688_; lean_object* v_congrInfo_689_; lean_object* v_defEqI_690_; lean_object* v_extensions_691_; lean_object* v_issues_692_; lean_object* v_instanceOverrides_693_; uint8_t v_debug_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_715_; 
v___x_681_ = lean_st_ref_take(v_a_601_);
v_canon_682_ = lean_ctor_get(v___x_681_, 10);
v_share_683_ = lean_ctor_get(v___x_681_, 0);
v_maxFVar_684_ = lean_ctor_get(v___x_681_, 1);
v_proofInstInfo_685_ = lean_ctor_get(v___x_681_, 2);
v_proofInstInfoFVar_686_ = lean_ctor_get(v___x_681_, 3);
v_inferType_687_ = lean_ctor_get(v___x_681_, 4);
v_getLevel_688_ = lean_ctor_get(v___x_681_, 5);
v_congrInfo_689_ = lean_ctor_get(v___x_681_, 6);
v_defEqI_690_ = lean_ctor_get(v___x_681_, 7);
v_extensions_691_ = lean_ctor_get(v___x_681_, 8);
v_issues_692_ = lean_ctor_get(v___x_681_, 9);
v_instanceOverrides_693_ = lean_ctor_get(v___x_681_, 11);
v_debug_694_ = lean_ctor_get_uint8(v___x_681_, sizeof(void*)*12);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_715_ == 0)
{
v___x_696_ = v___x_681_;
v_isShared_697_ = v_isSharedCheck_715_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_instanceOverrides_693_);
lean_inc(v_canon_682_);
lean_inc(v_issues_692_);
lean_inc(v_extensions_691_);
lean_inc(v_defEqI_690_);
lean_inc(v_congrInfo_689_);
lean_inc(v_getLevel_688_);
lean_inc(v_inferType_687_);
lean_inc(v_proofInstInfoFVar_686_);
lean_inc(v_proofInstInfo_685_);
lean_inc(v_maxFVar_684_);
lean_inc(v_share_683_);
lean_dec(v___x_681_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_715_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_cache_698_; lean_object* v_cacheInType_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_714_; 
v_cache_698_ = lean_ctor_get(v_canon_682_, 0);
v_cacheInType_699_ = lean_ctor_get(v_canon_682_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_canon_682_);
if (v_isSharedCheck_714_ == 0)
{
v___x_701_ = v_canon_682_;
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_cacheInType_699_);
lean_inc(v_cache_698_);
lean_dec(v_canon_682_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
lean_inc(v_a_677_);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_607_, v___x_608_, v_cacheInType_699_, v_e_597_, v_a_677_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_cache_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_713_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 10, v___x_705_);
v___x_707_ = v___x_696_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_share_683_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_maxFVar_684_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_proofInstInfo_685_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_proofInstInfoFVar_686_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_inferType_687_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_getLevel_688_);
lean_ctor_set(v_reuseFailAlloc_712_, 6, v_congrInfo_689_);
lean_ctor_set(v_reuseFailAlloc_712_, 7, v_defEqI_690_);
lean_ctor_set(v_reuseFailAlloc_712_, 8, v_extensions_691_);
lean_ctor_set(v_reuseFailAlloc_712_, 9, v_issues_692_);
lean_ctor_set(v_reuseFailAlloc_712_, 10, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 11, v_instanceOverrides_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*12, v_debug_694_);
v___x_707_ = v_reuseFailAlloc_712_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_st_ref_put(v_a_601_, v___x_707_);
if (v_isShared_680_ == 0)
{
v___x_710_ = v___x_679_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_677_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_597_);
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_717_, lean_object* v_k_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
uint8_t v_a_boxed_727_; lean_object* v_res_728_; 
v_a_boxed_727_ = lean_unbox(v_a_719_);
v_res_728_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_717_, v_k_718_, v_a_boxed_727_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
return v_res_728_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = l_Lean_Expr_cleanupAnnotations(v_e_735_);
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_738_ = l_Lean_Expr_isConstOf(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_Expr_isApp(v___x_736_);
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_736_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_736_);
v___x_741_ = l_Lean_Expr_isApp(v___x_740_);
if (v___x_741_ == 0)
{
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_736_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_740_);
v___x_743_ = l_Lean_Expr_isApp(v___x_742_);
if (v___x_743_ == 0)
{
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_736_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_742_);
lean_dec_ref(v___x_742_);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_746_ = l_Lean_Expr_isConstOf(v___x_744_, v___x_745_);
lean_dec_ref(v___x_744_);
if (v___x_746_ == 0)
{
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_736_);
return v___x_746_;
}
else
{
lean_object* v_arg_747_; uint8_t v___x_748_; 
v_arg_747_ = lean_ctor_get(v___x_740_, 1);
lean_inc_ref(v_arg_747_);
lean_dec_ref(v___x_740_);
v___x_748_ = l_Lean_Expr_isBoolTrue(v_arg_747_);
lean_dec_ref(v_arg_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v___x_736_);
return v___x_748_;
}
else
{
lean_object* v_arg_749_; uint8_t v___x_750_; 
v_arg_749_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_arg_749_);
lean_dec_ref(v___x_736_);
v___x_750_ = l_Lean_Expr_isBoolTrue(v_arg_749_);
lean_dec_ref(v_arg_749_);
return v___x_750_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_736_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_751_);
lean_dec_ref(v_e_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = l_Lean_Expr_cleanupAnnotations(v_e_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_760_ = l_Lean_Expr_isConstOf(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
uint8_t v___x_761_; 
v___x_761_ = l_Lean_Expr_isApp(v___x_758_);
if (v___x_761_ == 0)
{
lean_dec_ref(v___x_758_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_758_);
v___x_763_ = l_Lean_Expr_isApp(v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_758_);
return v___x_763_;
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_762_);
v___x_765_ = l_Lean_Expr_isApp(v___x_764_);
if (v___x_765_ == 0)
{
lean_dec_ref(v___x_764_);
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_758_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_764_);
lean_dec_ref(v___x_764_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_768_ = l_Lean_Expr_isConstOf(v___x_766_, v___x_767_);
lean_dec_ref(v___x_766_);
if (v___x_768_ == 0)
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_758_);
return v___x_768_;
}
else
{
lean_object* v_arg_769_; uint8_t v___x_770_; 
v_arg_769_ = lean_ctor_get(v___x_762_, 1);
lean_inc_ref(v_arg_769_);
lean_dec_ref(v___x_762_);
v___x_770_ = l_Lean_Expr_isBoolFalse(v_arg_769_);
lean_dec_ref(v_arg_769_);
if (v___x_770_ == 0)
{
lean_dec_ref(v___x_758_);
return v___x_770_;
}
else
{
lean_object* v_arg_771_; uint8_t v___x_772_; 
v_arg_771_ = lean_ctor_get(v___x_758_, 1);
lean_inc_ref(v_arg_771_);
lean_dec_ref(v___x_758_);
v___x_772_ = l_Lean_Expr_isBoolTrue(v_arg_771_);
lean_dec_ref(v_arg_771_);
return v___x_772_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_758_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_773_);
lean_dec_ref(v_e_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(uint8_t v_x_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(v_x_776_);
v___x_778_ = lean_obj_tag_nat(v___x_777_);
lean_dec(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl___boxed(lean_object* v_x_779_){
_start:
{
uint8_t v_x_4__boxed_780_; lean_object* v_res_781_; 
v_x_4__boxed_780_ = lean_unbox(v_x_779_);
v_res_781_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___impl(v_x_4__boxed_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_782_){
_start:
{
lean_inc(v_k_782_);
return v_k_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_783_);
lean_dec(v_k_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_785_, lean_object* v_ctorIdx_786_, uint8_t v_t_787_, lean_object* v_h_788_, lean_object* v_k_789_){
_start:
{
lean_inc(v_k_789_);
return v_k_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_790_, lean_object* v_ctorIdx_791_, lean_object* v_t_792_, lean_object* v_h_793_, lean_object* v_k_794_){
_start:
{
uint8_t v_t_boxed_795_; lean_object* v_res_796_; 
v_t_boxed_795_ = lean_unbox(v_t_792_);
v_res_796_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_790_, v_ctorIdx_791_, v_t_boxed_795_, v_h_793_, v_k_794_);
lean_dec(v_k_794_);
lean_dec(v_ctorIdx_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_797_){
_start:
{
lean_inc(v_canonType_797_);
return v_canonType_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_798_);
lean_dec(v_canonType_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_800_, uint8_t v_t_801_, lean_object* v_h_802_, lean_object* v_canonType_803_){
_start:
{
lean_inc(v_canonType_803_);
return v_canonType_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_804_, lean_object* v_t_805_, lean_object* v_h_806_, lean_object* v_canonType_807_){
_start:
{
uint8_t v_t_boxed_808_; lean_object* v_res_809_; 
v_t_boxed_808_ = lean_unbox(v_t_805_);
v_res_809_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_804_, v_t_boxed_808_, v_h_806_, v_canonType_807_);
lean_dec(v_canonType_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_810_){
_start:
{
lean_inc(v_canonInst_810_);
return v_canonInst_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_811_);
lean_dec(v_canonInst_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_813_, uint8_t v_t_814_, lean_object* v_h_815_, lean_object* v_canonInst_816_){
_start:
{
lean_inc(v_canonInst_816_);
return v_canonInst_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_817_, lean_object* v_t_818_, lean_object* v_h_819_, lean_object* v_canonInst_820_){
_start:
{
uint8_t v_t_boxed_821_; lean_object* v_res_822_; 
v_t_boxed_821_ = lean_unbox(v_t_818_);
v_res_822_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_817_, v_t_boxed_821_, v_h_819_, v_canonInst_820_);
lean_dec(v_canonInst_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_823_){
_start:
{
lean_inc(v_canonImplicit_823_);
return v_canonImplicit_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_824_);
lean_dec(v_canonImplicit_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_826_, uint8_t v_t_827_, lean_object* v_h_828_, lean_object* v_canonImplicit_829_){
_start:
{
lean_inc(v_canonImplicit_829_);
return v_canonImplicit_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_canonImplicit_833_){
_start:
{
uint8_t v_t_boxed_834_; lean_object* v_res_835_; 
v_t_boxed_834_ = lean_unbox(v_t_831_);
v_res_835_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_830_, v_t_boxed_834_, v_h_832_, v_canonImplicit_833_);
lean_dec(v_canonImplicit_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_836_){
_start:
{
lean_inc(v_visit_836_);
return v_visit_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_837_);
lean_dec(v_visit_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_839_, uint8_t v_t_840_, lean_object* v_h_841_, lean_object* v_visit_842_){
_start:
{
lean_inc(v_visit_842_);
return v_visit_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_843_, lean_object* v_t_844_, lean_object* v_h_845_, lean_object* v_visit_846_){
_start:
{
uint8_t v_t_boxed_847_; lean_object* v_res_848_; 
v_t_boxed_847_ = lean_unbox(v_t_844_);
v_res_848_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_843_, v_t_boxed_847_, v_h_845_, v_visit_846_);
lean_dec(v_visit_846_);
return v_res_848_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = 0;
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_863_, lean_object* v_x_864_){
_start:
{
switch(v_r_863_)
{
case 0:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_865_;
}
case 1:
{
lean_object* v___x_866_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_866_;
}
case 2:
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_867_;
}
default: 
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_869_, lean_object* v_x_870_){
_start:
{
uint8_t v_r_boxed_871_; lean_object* v_res_872_; 
v_r_boxed_871_ = lean_unbox(v_r_869_);
v_res_872_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_871_, v_x_870_);
lean_dec(v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_875_, lean_object* v_i_876_, lean_object* v_arg_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_pinfos_875_);
v___x_934_ = lean_nat_dec_lt(v_i_876_, v___x_933_);
if (v___x_934_ == 0)
{
v___y_884_ = v_a_878_;
v___y_885_ = v_a_879_;
v___y_886_ = v_a_880_;
v___y_887_ = v_a_881_;
goto v___jp_883_;
}
else
{
lean_object* v_pinfo_935_; uint8_t v_isInstance_936_; 
v_pinfo_935_ = lean_array_fget_borrowed(v_pinfos_875_, v_i_876_);
v_isInstance_936_ = lean_ctor_get_uint8(v_pinfo_935_, sizeof(void*)*1 + 4);
if (v_isInstance_936_ == 0)
{
uint8_t v_isProp_937_; 
v_isProp_937_ = lean_ctor_get_uint8(v_pinfo_935_, sizeof(void*)*1 + 2);
if (v_isProp_937_ == 0)
{
uint8_t v___x_938_; 
v___x_938_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_935_);
if (v___x_938_ == 0)
{
v___y_884_ = v_a_878_;
v___y_885_ = v_a_879_;
v___y_886_ = v_a_880_;
v___y_887_ = v_a_881_;
goto v___jp_883_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Meta_isTypeFormer(v_arg_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_955_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_955_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_955_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_955_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
uint8_t v___x_944_; 
v___x_944_ = lean_unbox(v_a_940_);
lean_dec(v_a_940_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = 2;
v___x_946_ = lean_box(v___x_945_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_946_);
v___x_948_ = v___x_942_;
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
else
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = 0;
v___x_951_ = lean_box(v___x_950_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_951_);
v___x_953_ = v___x_942_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_939_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_939_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_arg_877_);
v___x_964_ = 3;
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
else
{
uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec_ref(v_arg_877_);
v___x_967_ = 1;
v___x_968_ = lean_box(v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
v___jp_883_:
{
lean_object* v___x_888_; 
lean_inc_ref(v_arg_877_);
v___x_888_ = l_Lean_Meta_isProp(v_arg_877_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_924_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_924_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_924_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_924_;
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
v___x_894_ = l_Lean_Meta_isTypeFormer(v_arg_877_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_910_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_910_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
uint8_t v___x_899_; 
v___x_899_ = lean_unbox(v_a_895_);
lean_dec(v_a_895_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_900_ = 3;
v___x_901_ = lean_box(v___x_900_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_901_);
v___x_903_ = v___x_897_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
else
{
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_905_ = 0;
v___x_906_ = lean_box(v___x_905_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_906_);
v___x_908_ = v___x_897_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_894_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_894_);
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
else
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec_ref(v_arg_877_);
v___x_919_ = 3;
v___x_920_ = lean_box(v___x_919_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_920_);
v___x_922_ = v___x_891_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_arg_877_);
v_a_925_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_888_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_888_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_970_, lean_object* v_i_971_, lean_object* v_arg_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_970_, v_i_971_, v_arg_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_i_971_);
lean_dec_ref(v_pinfos_970_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(lean_object* v_e_979_, lean_object* v_offset_980_){
_start:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_nat_dec_eq(v_offset_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = l_Lean_mkNatLit(v_offset_980_);
v___x_984_ = l_Lean_mkNatAdd(v_e_979_, v___x_983_);
return v___x_984_;
}
else
{
lean_dec(v_offset_980_);
return v_e_979_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_985_; lean_object* v_dummy_986_; 
v___x_985_ = lean_box(0);
v_dummy_986_ = l_Lean_Expr_sort___override(v___x_985_);
return v_dummy_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_987_, lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
uint8_t v_fromClass_994_; 
v_fromClass_994_ = lean_ctor_get_uint8(v_info_987_, sizeof(void*)*3);
if (v_fromClass_994_ == 0)
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_988_, v_fromClass_994_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1031_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1031_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1031_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
if (lean_obj_tag(v_a_996_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_998_);
v_val_1000_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_a_996_, 1);
v___x_1001_ = l_Lean_Expr_getAppFn(v_val_1000_);
v___x_1002_ = l_Lean_Meta_reduceProj_x3f(v___x_1001_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
if (lean_obj_tag(v_a_1003_) == 0)
{
lean_dec(v_val_1000_);
return v___x_1002_;
}
else
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1025_; 
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1026_);
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1025_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1025_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1024_; 
v_val_1007_ = lean_ctor_get(v_a_1003_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_1003_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1009_ = v_a_1003_;
v_isShared_1010_ = v_isSharedCheck_1024_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_dec(v_a_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1024_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_dummy_1011_; lean_object* v_nargs_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v_dummy_1011_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_1012_ = l_Lean_Expr_getAppNumArgs(v_val_1000_);
lean_inc(v_nargs_1012_);
v___x_1013_ = lean_mk_array(v_nargs_1012_, v_dummy_1011_);
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_sub(v_nargs_1012_, v___x_1014_);
lean_dec(v_nargs_1012_);
v___x_1016_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_1000_, v___x_1013_, v___x_1015_);
v___x_1017_ = l_Lean_mkAppN(v_val_1007_, v___x_1016_);
lean_dec_ref(v___x_1016_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1017_);
v___x_1019_ = v___x_1009_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1019_);
v___x_1021_ = v___x_1005_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
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
else
{
lean_dec(v_val_1000_);
return v___x_1002_;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec(v_a_996_);
v___x_1027_ = lean_box(0);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1027_);
v___x_1029_ = v___x_998_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
return v___x_995_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_e_988_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_1034_, lean_object* v_e_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_1034_, v_e_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec_ref(v_info_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_1042_, lean_object* v_e_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_1042_, v_e_1043_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_1052_, lean_object* v_e_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_1052_, v_e_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_info_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_1062_){
_start:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg___closed__3));
v___x_1064_ = l_Lean_Expr_isConstOf(v_e_1062_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_1065_);
lean_dec_ref(v_e_1065_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = l_Lean_Expr_cleanupAnnotations(v_e_1101_);
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_1104_ = l_Lean_Expr_isConstOf(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_Expr_isApp(v___x_1102_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v___x_1102_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1102_);
lean_dec_ref(v___x_1102_);
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_1108_ = l_Lean_Expr_isConstOf(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_Expr_isApp(v___x_1106_);
if (v___x_1109_ == 0)
{
lean_dec_ref(v___x_1106_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1113_ = l_Lean_Expr_isApp(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1115_ = l_Lean_Expr_isApp(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v___x_1114_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1117_ = l_Lean_Expr_isApp(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v_arg_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_arg_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc_ref(v_arg_1118_);
v___x_1119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_1121_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_1123_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_1125_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_1127_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_1129_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1128_);
lean_dec_ref(v___x_1119_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v_arg_1118_);
return v___x_1129_;
}
else
{
uint8_t v___x_1130_; 
v___x_1130_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1118_);
lean_dec_ref(v_arg_1118_);
return v___x_1130_;
}
}
else
{
uint8_t v___x_1131_; 
lean_dec_ref(v___x_1119_);
v___x_1131_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1118_);
lean_dec_ref(v_arg_1118_);
return v___x_1131_;
}
}
else
{
uint8_t v___x_1132_; 
lean_dec_ref(v___x_1119_);
v___x_1132_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1118_);
lean_dec_ref(v_arg_1118_);
return v___x_1132_;
}
}
else
{
uint8_t v___x_1133_; 
lean_dec_ref(v___x_1119_);
v___x_1133_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1118_);
lean_dec_ref(v_arg_1118_);
return v___x_1133_;
}
}
else
{
uint8_t v___x_1134_; 
lean_dec_ref(v___x_1119_);
v___x_1134_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_1118_);
lean_dec_ref(v_arg_1118_);
return v___x_1134_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1106_);
return v___x_1108_;
}
}
}
else
{
lean_dec_ref(v___x_1102_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_1135_);
lean_dec_ref(v_e_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_1144_, lean_object* v_inst_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
lean_inc_ref(v_inst_1145_);
lean_inc_ref(v_e_1144_);
v___x_1153_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_1144_, v_inst_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1204_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1204_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1204_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_unbox(v_a_1154_);
lean_dec(v_a_1154_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_1156_);
v___x_1159_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1144_);
v___x_1160_ = l_Lean_indentExpr(v_e_1144_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_indentExpr(v_inst_1145_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1146_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1192_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1192_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1192_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v_verbose_1171_; 
v_verbose_1171_ = lean_ctor_get_uint8(v_a_1167_, 0);
lean_dec(v_a_1167_);
if (v_verbose_1171_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref_known(v___x_1165_, 2);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_e_1144_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_e_1144_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
lean_object* v___x_1175_; 
lean_del_object(v___x_1169_);
v___x_1175_ = l_Lean_Meta_Sym_reportIssue(v___x_1165_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1183_);
v___x_1177_ = v___x_1175_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v___x_1175_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_e_1144_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_e_1144_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_e_1144_);
v_a_1184_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1175_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref_known(v___x_1165_, 2);
lean_dec_ref(v_e_1144_);
v_a_1193_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1166_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1166_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec_ref(v_e_1144_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_inst_1145_);
v___x_1202_ = v___x_1156_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_inst_1145_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_e_1144_);
v_a_1205_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1153_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1153_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_1213_, lean_object* v_inst_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1213_, v_inst_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15___redArg(lean_object* v_a_1223_, lean_object* v_b_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_dec(v_b_1224_);
lean_dec_ref(v_a_1223_);
return v_x_1225_;
}
else
{
lean_object* v_key_1226_; lean_object* v_value_1227_; lean_object* v_tail_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1240_; 
v_key_1226_ = lean_ctor_get(v_x_1225_, 0);
v_value_1227_ = lean_ctor_get(v_x_1225_, 1);
v_tail_1228_ = lean_ctor_get(v_x_1225_, 2);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1230_ = v_x_1225_;
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_tail_1228_);
lean_inc(v_value_1227_);
lean_inc(v_key_1226_);
lean_dec(v_x_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_expr_eqv(v_key_1226_, v_a_1223_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15___redArg(v_a_1223_, v_b_1224_, v_tail_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 2, v___x_1233_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_key_1226_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_value_1227_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_value_1227_);
lean_dec(v_key_1226_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v_b_1224_);
lean_ctor_set(v___x_1230_, 0, v_a_1223_);
v___x_1238_ = v___x_1230_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1223_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_b_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_tail_1228_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_a_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 0;
return v___x_1243_;
}
else
{
lean_object* v_key_1244_; lean_object* v_tail_1245_; uint8_t v___x_1246_; 
v_key_1244_ = lean_ctor_get(v_x_1242_, 0);
v_tail_1245_ = lean_ctor_get(v_x_1242_, 2);
v___x_1246_ = lean_expr_eqv(v_key_1244_, v_a_1241_);
if (v___x_1246_ == 0)
{
v_x_1242_ = v_tail_1245_;
goto _start;
}
else
{
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg___boxed(lean_object* v_a_1248_, lean_object* v_x_1249_){
_start:
{
uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_a_1248_, v_x_1249_);
lean_dec(v_x_1249_);
lean_dec_ref(v_a_1248_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36___redArg(lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
return v_x_1252_;
}
else
{
lean_object* v_key_1254_; lean_object* v_value_1255_; lean_object* v_tail_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1279_; 
v_key_1254_ = lean_ctor_get(v_x_1253_, 0);
v_value_1255_ = lean_ctor_get(v_x_1253_, 1);
v_tail_1256_ = lean_ctor_get(v_x_1253_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1258_ = v_x_1253_;
v_isShared_1259_ = v_isSharedCheck_1279_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_tail_1256_);
lean_inc(v_value_1255_);
lean_inc(v_key_1254_);
lean_dec(v_x_1253_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1279_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; uint64_t v___x_1261_; uint64_t v___x_1262_; uint64_t v___x_1263_; uint64_t v_fold_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1260_ = lean_array_get_size(v_x_1252_);
v___x_1261_ = l_Lean_Expr_hash(v_key_1254_);
v___x_1262_ = 32ULL;
v___x_1263_ = lean_uint64_shift_right(v___x_1261_, v___x_1262_);
v_fold_1264_ = lean_uint64_xor(v___x_1261_, v___x_1263_);
v___x_1265_ = 16ULL;
v___x_1266_ = lean_uint64_shift_right(v_fold_1264_, v___x_1265_);
v___x_1267_ = lean_uint64_xor(v_fold_1264_, v___x_1266_);
v___x_1268_ = lean_uint64_to_usize(v___x_1267_);
v___x_1269_ = lean_usize_of_nat(v___x_1260_);
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_sub(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_usize_land(v___x_1268_, v___x_1271_);
v___x_1273_ = lean_array_uget_borrowed(v_x_1252_, v___x_1272_);
lean_inc(v___x_1273_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 2, v___x_1273_);
v___x_1275_ = v___x_1258_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_key_1254_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_value_1255_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_array_uset(v_x_1252_, v___x_1272_, v___x_1275_);
v_x_1252_ = v___x_1276_;
v_x_1253_ = v_tail_1256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31___redArg(lean_object* v_i_1280_, lean_object* v_source_1281_, lean_object* v_target_1282_){
_start:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_array_get_size(v_source_1281_);
v___x_1284_ = lean_nat_dec_lt(v_i_1280_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec_ref(v_source_1281_);
lean_dec(v_i_1280_);
return v_target_1282_;
}
else
{
lean_object* v_es_1285_; lean_object* v___x_1286_; lean_object* v_source_1287_; lean_object* v_target_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_es_1285_ = lean_array_fget(v_source_1281_, v_i_1280_);
v___x_1286_ = lean_box(0);
v_source_1287_ = lean_array_fset(v_source_1281_, v_i_1280_, v___x_1286_);
v_target_1288_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36___redArg(v_target_1282_, v_es_1285_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_add(v_i_1280_, v___x_1289_);
lean_dec(v_i_1280_);
v_i_1280_ = v___x_1290_;
v_source_1281_ = v_source_1287_;
v_target_1282_ = v_target_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_data_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_nbuckets_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1293_ = lean_array_get_size(v_data_1292_);
v___x_1294_ = lean_unsigned_to_nat(2u);
v_nbuckets_1295_ = lean_nat_mul(v___x_1293_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_mk_array(v_nbuckets_1295_, v___x_1297_);
v___x_1299_ = lean_array_propagate_mark(v_data_1292_, v___x_1298_);
v___x_1300_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31___redArg(v___x_1296_, v_data_1292_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_){
_start:
{
lean_object* v_size_1304_; lean_object* v_buckets_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1348_; 
v_size_1304_ = lean_ctor_get(v_m_1301_, 0);
v_buckets_1305_ = lean_ctor_get(v_m_1301_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_m_1301_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1307_ = v_m_1301_;
v_isShared_1308_ = v_isSharedCheck_1348_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_buckets_1305_);
lean_inc(v_size_1304_);
lean_dec(v_m_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1348_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v_fold_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v_bkt_1322_; uint8_t v___x_1323_; 
v___x_1309_ = lean_array_get_size(v_buckets_1305_);
v___x_1310_ = l_Lean_Expr_hash(v_a_1302_);
v___x_1311_ = 32ULL;
v___x_1312_ = lean_uint64_shift_right(v___x_1310_, v___x_1311_);
v_fold_1313_ = lean_uint64_xor(v___x_1310_, v___x_1312_);
v___x_1314_ = 16ULL;
v___x_1315_ = lean_uint64_shift_right(v_fold_1313_, v___x_1314_);
v___x_1316_ = lean_uint64_xor(v_fold_1313_, v___x_1315_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = lean_usize_of_nat(v___x_1309_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_sub(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_usize_land(v___x_1317_, v___x_1320_);
v_bkt_1322_ = lean_array_uget_borrowed(v_buckets_1305_, v___x_1321_);
v___x_1323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_a_1302_, v_bkt_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v_size_x27_1325_; lean_object* v___x_1326_; lean_object* v_buckets_x27_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v_size_x27_1325_ = lean_nat_add(v_size_1304_, v___x_1324_);
lean_dec(v_size_1304_);
lean_inc(v_bkt_1322_);
v___x_1326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1326_, 0, v_a_1302_);
lean_ctor_set(v___x_1326_, 1, v_b_1303_);
lean_ctor_set(v___x_1326_, 2, v_bkt_1322_);
v_buckets_x27_1327_ = lean_array_uset(v_buckets_1305_, v___x_1321_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = lean_nat_mul(v_size_x27_1325_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_nat_div(v___x_1329_, v___x_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_array_get_size(v_buckets_x27_1327_);
v___x_1333_ = lean_nat_dec_le(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
if (v___x_1333_ == 0)
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
v_val_1334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_buckets_x27_1327_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_val_1334_);
lean_ctor_set(v___x_1307_, 0, v_size_x27_1325_);
v___x_1336_ = v___x_1307_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v___x_1339_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_buckets_x27_1327_);
lean_ctor_set(v___x_1307_, 0, v_size_x27_1325_);
v___x_1339_ = v___x_1307_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_buckets_x27_1327_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v_buckets_x27_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_inc(v_bkt_1322_);
v___x_1341_ = lean_box(0);
v_buckets_x27_1342_ = lean_array_uset(v_buckets_1305_, v___x_1321_, v___x_1341_);
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15___redArg(v_a_1302_, v_b_1303_, v_bkt_1322_);
v___x_1344_ = lean_array_uset(v_buckets_x27_1342_, v___x_1321_, v___x_1343_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1344_);
v___x_1346_ = v___x_1307_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_size_1304_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0(lean_object* v_k_1349_, uint8_t v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(v___y_1350_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
v___x_1360_ = lean_apply_9(v_k_1349_, v_b_1353_, v___x_1359_, v___y_1351_, v___y_1352_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0___boxed(lean_object* v_k_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v___y_68531__boxed_1371_; lean_object* v_res_1372_; 
v___y_68531__boxed_1371_ = lean_unbox(v___y_1362_);
v_res_1372_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0(v_k_1361_, v___y_68531__boxed_1371_, v___y_1363_, v___y_1364_, v_b_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(lean_object* v_name_1373_, uint8_t v_bi_1374_, lean_object* v_type_1375_, lean_object* v_k_1376_, uint8_t v_kind_1377_, uint8_t v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_box(v___y_1378_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1387_, 0, v_k_1376_);
lean_closure_set(v___f_1387_, 1, v___x_1386_);
lean_closure_set(v___f_1387_, 2, v___y_1379_);
lean_closure_set(v___f_1387_, 3, v___y_1380_);
v___x_1388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1373_, v_bi_1374_, v_type_1375_, v___f_1387_, v_kind_1377_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg___boxed(lean_object* v_name_1397_, lean_object* v_bi_1398_, lean_object* v_type_1399_, lean_object* v_k_1400_, lean_object* v_kind_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_bi_boxed_1410_; uint8_t v_kind_boxed_1411_; uint8_t v___y_68559__boxed_1412_; lean_object* v_res_1413_; 
v_bi_boxed_1410_ = lean_unbox(v_bi_1398_);
v_kind_boxed_1411_ = lean_unbox(v_kind_1401_);
v___y_68559__boxed_1412_ = lean_unbox(v___y_1402_);
v_res_1413_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(v_name_1397_, v_bi_boxed_1410_, v_type_1399_, v_k_1400_, v_kind_boxed_1411_, v___y_68559__boxed_1412_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_env_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1417_ = lean_st_ref_get(v___y_1415_);
v_env_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1418_);
lean_dec(v___x_1417_);
v___x_1419_ = l_Lean_Meta_isMatcherCore(v_env_1418_, v_declName_1414_);
v___x_1420_ = lean_box(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1422_, v___y_1423_);
lean_dec(v___y_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(lean_object* v_declName_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v_env_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = lean_st_ref_get(v___y_1427_);
v_env_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc_ref(v_env_1430_);
lean_dec(v___x_1429_);
v___x_1431_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1430_, v_declName_1426_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg___boxed(lean_object* v_declName_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1433_, v___y_1434_);
lean_dec(v___y_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24(lean_object* v_msgData_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; lean_object* v_env_1444_; uint8_t v___x_1445_; lean_object* v_env_1446_; lean_object* v___x_1447_; lean_object* v_toCold_1448_; lean_object* v_mctx_1449_; lean_object* v_lctx_1450_; lean_object* v_options_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1443_ = lean_st_ref_get(v___y_1441_);
v_env_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_ref(v_env_1444_);
lean_dec(v___x_1443_);
v___x_1445_ = 0;
v_env_1446_ = l_Lean_Environment_setRecordingDeps(v_env_1444_, v___x_1445_);
v___x_1447_ = lean_st_ref_get(v___y_1439_);
v_toCold_1448_ = lean_ctor_get(v___y_1440_, 0);
v_mctx_1449_ = lean_ctor_get(v___x_1447_, 0);
lean_inc_ref(v_mctx_1449_);
lean_dec(v___x_1447_);
v_lctx_1450_ = lean_ctor_get(v___y_1438_, 2);
v_options_1451_ = lean_ctor_get(v_toCold_1448_, 2);
lean_inc_ref(v_options_1451_);
lean_inc_ref(v_lctx_1450_);
v___x_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1452_, 0, v_env_1446_);
lean_ctor_set(v___x_1452_, 1, v_mctx_1449_);
lean_ctor_set(v___x_1452_, 2, v_lctx_1450_);
lean_ctor_set(v___x_1452_, 3, v_options_1451_);
v___x_1453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_msgData_1437_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24___boxed(lean_object* v_msgData_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24(v_msgData_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1461_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1462_; double v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_float_of_nat(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(lean_object* v_cls_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_ref_1474_; lean_object* v___x_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1521_; 
v_ref_1474_ = lean_ctor_get(v___y_1471_, 2);
v___x_1475_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11_spec__24(v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v_traceState_1481_; lean_object* v_env_1482_; lean_object* v_nextMacroScope_1483_; lean_object* v_ngen_1484_; lean_object* v_auxDeclNGen_1485_; lean_object* v_cache_1486_; lean_object* v_recordedDeps_1487_; lean_object* v_messages_1488_; lean_object* v_infoState_1489_; lean_object* v_snapshotTasks_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1520_; 
v___x_1480_ = lean_st_ref_take(v___y_1472_);
v_traceState_1481_ = lean_ctor_get(v___x_1480_, 4);
v_env_1482_ = lean_ctor_get(v___x_1480_, 0);
v_nextMacroScope_1483_ = lean_ctor_get(v___x_1480_, 1);
v_ngen_1484_ = lean_ctor_get(v___x_1480_, 2);
v_auxDeclNGen_1485_ = lean_ctor_get(v___x_1480_, 3);
v_cache_1486_ = lean_ctor_get(v___x_1480_, 5);
v_recordedDeps_1487_ = lean_ctor_get(v___x_1480_, 6);
v_messages_1488_ = lean_ctor_get(v___x_1480_, 7);
v_infoState_1489_ = lean_ctor_get(v___x_1480_, 8);
v_snapshotTasks_1490_ = lean_ctor_get(v___x_1480_, 9);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1492_ = v___x_1480_;
v_isShared_1493_ = v_isSharedCheck_1520_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_snapshotTasks_1490_);
lean_inc(v_infoState_1489_);
lean_inc(v_messages_1488_);
lean_inc(v_recordedDeps_1487_);
lean_inc(v_cache_1486_);
lean_inc(v_traceState_1481_);
lean_inc(v_auxDeclNGen_1485_);
lean_inc(v_ngen_1484_);
lean_inc(v_nextMacroScope_1483_);
lean_inc(v_env_1482_);
lean_dec(v___x_1480_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1520_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint64_t v_tid_1494_; lean_object* v_traces_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1519_; 
v_tid_1494_ = lean_ctor_get_uint64(v_traceState_1481_, sizeof(void*)*1);
v_traces_1495_ = lean_ctor_get(v_traceState_1481_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_traceState_1481_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1497_ = v_traceState_1481_;
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_traces_1495_);
lean_dec(v_traceState_1481_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; double v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__0);
v___x_1502_ = 0;
v___x_1503_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__1));
v___x_1504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1504_, 0, v_cls_1467_);
lean_ctor_set(v___x_1504_, 1, v___x_1500_);
lean_ctor_set(v___x_1504_, 2, v___x_1503_);
lean_ctor_set_float(v___x_1504_, sizeof(void*)*3, v___x_1501_);
lean_ctor_set_float(v___x_1504_, sizeof(void*)*3 + 8, v___x_1501_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*3 + 16, v___x_1502_);
v___x_1505_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___closed__2));
v___x_1506_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v_a_1476_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
lean_inc(v_ref_1474_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_ref_1474_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_PersistentArray_push___redArg(v_traces_1495_, v___x_1507_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1508_);
v___x_1510_ = v___x_1497_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
lean_ctor_set_uint64(v_reuseFailAlloc_1518_, sizeof(void*)*1, v_tid_1494_);
v___x_1510_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v___x_1510_);
v___x_1512_ = v___x_1492_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_env_1482_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_nextMacroScope_1483_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_ngen_1484_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_auxDeclNGen_1485_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 5, v_cache_1486_);
lean_ctor_set(v_reuseFailAlloc_1517_, 6, v_recordedDeps_1487_);
lean_ctor_set(v_reuseFailAlloc_1517_, 7, v_messages_1488_);
lean_ctor_set(v_reuseFailAlloc_1517_, 8, v_infoState_1489_);
lean_ctor_set(v_reuseFailAlloc_1517_, 9, v_snapshotTasks_1490_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_st_ref_put(v___y_1472_, v___x_1512_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1499_);
v___x_1515_ = v___x_1478_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1499_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg___boxed(lean_object* v_cls_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_1522_, v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg(lean_object* v_a_1530_, lean_object* v_x_1531_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
else
{
lean_object* v_key_1533_; lean_object* v_value_1534_; lean_object* v_tail_1535_; uint8_t v___x_1536_; 
v_key_1533_ = lean_ctor_get(v_x_1531_, 0);
v_value_1534_ = lean_ctor_get(v_x_1531_, 1);
v_tail_1535_ = lean_ctor_get(v_x_1531_, 2);
v___x_1536_ = lean_expr_eqv(v_key_1533_, v_a_1530_);
if (v___x_1536_ == 0)
{
v_x_1531_ = v_tail_1535_;
goto _start;
}
else
{
lean_object* v___x_1538_; 
lean_inc(v_value_1534_);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_value_1534_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg___boxed(lean_object* v_a_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg(v_a_1539_, v_x_1540_);
lean_dec(v_x_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_buckets_1544_; lean_object* v___x_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v_fold_1549_; uint64_t v___x_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_buckets_1544_ = lean_ctor_get(v_m_1542_, 1);
v___x_1545_ = lean_array_get_size(v_buckets_1544_);
v___x_1546_ = l_Lean_Expr_hash(v_a_1543_);
v___x_1547_ = 32ULL;
v___x_1548_ = lean_uint64_shift_right(v___x_1546_, v___x_1547_);
v_fold_1549_ = lean_uint64_xor(v___x_1546_, v___x_1548_);
v___x_1550_ = 16ULL;
v___x_1551_ = lean_uint64_shift_right(v_fold_1549_, v___x_1550_);
v___x_1552_ = lean_uint64_xor(v_fold_1549_, v___x_1551_);
v___x_1553_ = lean_uint64_to_usize(v___x_1552_);
v___x_1554_ = lean_usize_of_nat(v___x_1545_);
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_sub(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_usize_land(v___x_1553_, v___x_1556_);
v___x_1558_ = lean_array_uget_borrowed(v_buckets_1544_, v___x_1557_);
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg(v_a_1543_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1560_, v_a_1561_);
lean_dec_ref(v_a_1561_);
lean_dec_ref(v_m_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg(lean_object* v_name_1563_, lean_object* v_type_1564_, lean_object* v_val_1565_, lean_object* v_k_1566_, uint8_t v_nondep_1567_, uint8_t v_kind_1568_, uint8_t v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(v___y_1569_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1578_, 0, v_k_1566_);
lean_closure_set(v___f_1578_, 1, v___x_1577_);
lean_closure_set(v___f_1578_, 2, v___y_1570_);
lean_closure_set(v___f_1578_, 3, v___y_1571_);
v___x_1579_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1563_, v_type_1564_, v_val_1565_, v___f_1578_, v_nondep_1567_, v_kind_1568_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
return v___x_1579_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg___boxed(lean_object* v_name_1588_, lean_object* v_type_1589_, lean_object* v_val_1590_, lean_object* v_k_1591_, lean_object* v_nondep_1592_, lean_object* v_kind_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_nondep_boxed_1602_; uint8_t v_kind_boxed_1603_; uint8_t v___y_68808__boxed_1604_; lean_object* v_res_1605_; 
v_nondep_boxed_1602_ = lean_unbox(v_nondep_1592_);
v_kind_boxed_1603_ = lean_unbox(v_kind_1593_);
v___y_68808__boxed_1604_ = lean_unbox(v___y_1594_);
v_res_1605_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg(v_name_1588_, v_type_1589_, v_val_1590_, v_k_1591_, v_nondep_boxed_1602_, v_kind_boxed_1603_, v___y_68808__boxed_1604_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_Lean_instInhabitedExpr;
v___x_1608_ = lean_panic_fn_borrowed(v___x_1607_, v_msg_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_1609_, lean_object* v_body_1610_, lean_object* v_x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
uint8_t v___y_68995__boxed_1620_; lean_object* v_res_1621_; 
v___y_68995__boxed_1620_ = lean_unbox(v___y_1612_);
v_res_1621_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_1609_, v_body_1610_, v_x_1611_, v___y_68995__boxed_1620_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1624_, lean_object* v_body_1625_, lean_object* v_x_1626_, uint8_t v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_array_push(v_fvars_1624_, v_x_1626_);
v___x_1636_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1635_, v_body_1625_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1637_, lean_object* v_body_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___y_69006__boxed_1648_; lean_object* v_res_1649_; 
v___y_69006__boxed_1648_ = lean_unbox(v___y_1640_);
v_res_1649_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1637_, v_body_1638_, v_x_1639_, v___y_69006__boxed_1648_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1650_, lean_object* v_e_1651_, uint8_t v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
if (lean_obj_tag(v_e_1651_) == 6)
{
lean_object* v_binderName_1660_; lean_object* v_binderType_1661_; lean_object* v_body_1662_; uint8_t v_binderInfo_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_binderName_1660_ = lean_ctor_get(v_e_1651_, 0);
lean_inc(v_binderName_1660_);
v_binderType_1661_ = lean_ctor_get(v_e_1651_, 1);
lean_inc_ref(v_binderType_1661_);
v_body_1662_ = lean_ctor_get(v_e_1651_, 2);
lean_inc_ref(v_body_1662_);
v_binderInfo_1663_ = lean_ctor_get_uint8(v_e_1651_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1651_, 3);
lean_inc_ref(v_fvars_1650_);
v___f_1664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1664_, 0, v_fvars_1650_);
lean_closure_set(v___f_1664_, 1, v_body_1662_);
v___x_1665_ = lean_expr_instantiate_rev(v_binderType_1661_, v_fvars_1650_);
lean_dec_ref(v_fvars_1650_);
lean_dec_ref(v_binderType_1661_);
v___x_1666_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1665_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = 0;
v___x_1669_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(v_binderName_1660_, v_binderInfo_1663_, v_a_1667_, v___f_1664_, v___x_1668_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
return v___x_1669_;
}
else
{
lean_dec_ref(v___f_1664_);
lean_dec(v_binderName_1660_);
return v___x_1666_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_expr_instantiate_rev(v_e_1651_, v_fvars_1650_);
lean_dec_ref(v_e_1651_);
v___x_1671_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1670_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; uint8_t v___x_1673_; uint8_t v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = 0;
v___x_1674_ = 1;
v___x_1675_ = 1;
v___x_1676_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1650_, v_a_1672_, v___x_1673_, v___x_1674_, v___x_1673_, v___x_1674_, v___x_1675_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec_ref(v_fvars_1650_);
return v___x_1676_;
}
else
{
lean_dec_ref(v_fvars_1650_);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1677_, uint8_t v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
if (v_a_1678_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1687_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1686_, v_e_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1689_ = l_Lean_Meta_Sym_etaReduce(v_e_1677_);
lean_dec_ref(v_e_1677_);
v___x_1690_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1688_, v___x_1689_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1691_, lean_object* v_body_1692_, lean_object* v_x_1693_, uint8_t v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_array_push(v_fvars_1691_, v_x_1693_);
v___x_1703_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1702_, v_body_1692_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1704_, lean_object* v_body_1705_, lean_object* v_x_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___y_69017__boxed_1715_; lean_object* v_res_1716_; 
v___y_69017__boxed_1715_ = lean_unbox(v___y_1707_);
v_res_1716_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1704_, v_body_1705_, v_x_1706_, v___y_69017__boxed_1715_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1717_, lean_object* v_e_1718_, uint8_t v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
if (lean_obj_tag(v_e_1718_) == 8)
{
lean_object* v_declName_1727_; lean_object* v_type_1728_; lean_object* v_value_1729_; lean_object* v_body_1730_; uint8_t v_nondep_1731_; lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_declName_1727_ = lean_ctor_get(v_e_1718_, 0);
lean_inc(v_declName_1727_);
v_type_1728_ = lean_ctor_get(v_e_1718_, 1);
lean_inc_ref(v_type_1728_);
v_value_1729_ = lean_ctor_get(v_e_1718_, 2);
lean_inc_ref(v_value_1729_);
v_body_1730_ = lean_ctor_get(v_e_1718_, 3);
lean_inc_ref(v_body_1730_);
v_nondep_1731_ = lean_ctor_get_uint8(v_e_1718_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1718_, 4);
lean_inc_ref(v_fvars_1717_);
v___f_1732_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1732_, 0, v_fvars_1717_);
lean_closure_set(v___f_1732_, 1, v_body_1730_);
v___x_1733_ = lean_expr_instantiate_rev(v_type_1728_, v_fvars_1717_);
lean_dec_ref(v_type_1728_);
v___x_1734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1733_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = lean_expr_instantiate_rev(v_value_1729_, v_fvars_1717_);
lean_dec_ref(v_fvars_1717_);
lean_dec_ref(v_value_1729_);
v___x_1737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1736_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = 0;
v___x_1740_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg(v_declName_1727_, v_a_1735_, v_a_1738_, v___f_1732_, v_nondep_1731_, v___x_1739_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1740_;
}
else
{
lean_dec(v_a_1735_);
lean_dec_ref(v___f_1732_);
lean_dec(v_declName_1727_);
return v___x_1737_;
}
}
else
{
lean_dec_ref(v___f_1732_);
lean_dec_ref(v_value_1729_);
lean_dec(v_declName_1727_);
lean_dec_ref(v_fvars_1717_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_expr_instantiate_rev(v_e_1718_, v_fvars_1717_);
lean_dec_ref(v_e_1718_);
v___x_1742_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1741_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = 1;
v___x_1745_ = 0;
v___x_1746_ = 1;
v___x_1747_ = l_Lean_Meta_mkLetFVars(v_fvars_1717_, v_a_1743_, v___x_1744_, v___x_1745_, v___x_1746_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec_ref(v_fvars_1717_);
return v___x_1747_;
}
else
{
lean_dec_ref(v_fvars_1717_);
return v___x_1742_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__0));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1753_, lean_object* v_type_1754_, uint8_t v_report_1755_, uint8_t v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___x_1814_; 
lean_inc_ref(v_type_1754_);
v___x_1814_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1754_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
if (lean_obj_tag(v_a_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v_type_1754_);
v_val_1816_ = lean_ctor_get(v_a_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v_a_1815_, 1);
v___x_1817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1753_, v_val_1816_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_a_1815_);
v___x_1818_ = l_Lean_Expr_getAppFn(v_e_1753_);
if (lean_obj_tag(v___x_1818_) == 4)
{
lean_object* v_declName_1819_; lean_object* v___x_1820_; 
v_declName_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_declName_1819_);
lean_dec_ref_known(v___x_1818_, 2);
v___x_1820_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_1819_, v_a_1762_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
if (lean_obj_tag(v_a_1821_) == 1)
{
lean_object* v_val_1822_; uint8_t v___x_1823_; 
v_val_1822_ = lean_ctor_get(v_a_1821_, 0);
lean_inc(v_val_1822_);
lean_dec_ref_known(v_a_1821_, 1);
v___x_1823_ = l_Lean_Expr_isApp(v_e_1753_);
if (v___x_1823_ == 0)
{
lean_dec(v_val_1822_);
v___y_1765_ = v_a_1757_;
v___y_1766_ = v_a_1758_;
v___y_1767_ = v_a_1759_;
v___y_1768_ = v_a_1760_;
v___y_1769_ = v_a_1761_;
v___y_1770_ = v_a_1762_;
goto v___jp_1764_;
}
else
{
uint8_t v_fromClass_1824_; 
v_fromClass_1824_ = lean_ctor_get_uint8(v_val_1822_, sizeof(void*)*3);
lean_dec(v_val_1822_);
if (v_fromClass_1824_ == 0)
{
v___y_1765_ = v_a_1757_;
v___y_1766_ = v_a_1758_;
v___y_1767_ = v_a_1759_;
v___y_1768_ = v_a_1760_;
v___y_1769_ = v_a_1761_;
v___y_1770_ = v_a_1762_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1825_; 
lean_dec_ref(v_type_1754_);
v___x_1825_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_1753_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
return v___x_1825_;
}
}
}
else
{
lean_dec(v_a_1821_);
v___y_1765_ = v_a_1757_;
v___y_1766_ = v_a_1758_;
v___y_1767_ = v_a_1759_;
v___y_1768_ = v_a_1760_;
v___y_1769_ = v_a_1761_;
v___y_1770_ = v_a_1762_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_type_1754_);
lean_dec_ref(v_e_1753_);
v_a_1826_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1820_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1820_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_dec_ref(v___x_1818_);
v___y_1765_ = v_a_1757_;
v___y_1766_ = v_a_1758_;
v___y_1767_ = v_a_1759_;
v___y_1768_ = v_a_1760_;
v___y_1769_ = v_a_1761_;
v___y_1770_ = v_a_1762_;
goto v___jp_1764_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_type_1754_);
lean_dec_ref(v_e_1753_);
v_a_1834_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1814_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1814_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
v___jp_1764_:
{
if (v_report_1755_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_type_1754_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_e_1753_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1772_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1753_);
v___x_1773_ = l_Lean_indentExpr(v_e_1753_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___closed__1);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_indentExpr(v_type_1754_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1765_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1805_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1805_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1805_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
uint8_t v_verbose_1784_; 
v_verbose_1784_ = lean_ctor_get_uint8(v_a_1780_, 0);
lean_dec(v_a_1780_);
if (v_verbose_1784_ == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v___x_1778_, 2);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v_e_1753_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_e_1753_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1782_);
v___x_1788_ = l_Lean_Meta_Sym_reportIssue(v___x_1778_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1788_, 0);
lean_dec(v_unused_1796_);
v___x_1790_ = v___x_1788_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v___x_1788_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_e_1753_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_e_1753_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_e_1753_);
v_a_1797_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1788_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1788_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref_known(v___x_1778_, 2);
lean_dec_ref(v_e_1753_);
v_a_1806_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1779_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1779_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst(lean_object* v_ofNat_1842_, lean_object* v_00_u03b1_1843_, lean_object* v_n_1844_, lean_object* v_inst_1845_, uint8_t v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___closed__0));
v___x_1855_ = l_Lean_Expr_constLevels_x21(v_ofNat_1842_);
v___x_1856_ = l_Lean_mkConst(v___x_1854_, v___x_1855_);
v___x_1857_ = l_Lean_mkAppB(v___x_1856_, v_00_u03b1_1843_, v_n_1844_);
v___x_1858_ = 1;
v___x_1859_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_inst_1845_, v___x_1857_, v___x_1858_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1860_, uint8_t v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
if (v_a_1861_ == 0)
{
uint8_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = 1;
v___x_1870_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1860_, v___x_1869_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1872_, uint8_t v_report_1873_, uint8_t v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; 
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
lean_inc(v_a_1878_);
lean_inc_ref(v_a_1877_);
lean_inc_ref(v_e_1872_);
v___x_1882_ = lean_infer_type(v_e_1872_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc_n(v_a_1883_, 2);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = l_Lean_Meta_isProp(v_a_1883_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1897_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
if (v_a_1874_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_unbox(v_a_1885_);
lean_dec(v_a_1885_);
if (v___x_1893_ == 0)
{
lean_del_object(v___x_1887_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_a_1883_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_e_1872_);
v___x_1895_ = v___x_1887_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_e_1872_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_del_object(v___x_1887_);
lean_dec(v_a_1885_);
goto v___jp_1889_;
}
v___jp_1889_:
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1883_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1872_, v_a_1891_, v_report_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1892_;
}
else
{
lean_dec_ref(v_e_1872_);
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1883_);
lean_dec_ref(v_e_1872_);
v_a_1898_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1884_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1884_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_dec_ref(v_e_1872_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1906_, uint8_t v_report_1907_, uint8_t v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
if (v_a_1908_ == 0)
{
lean_object* v___x_1916_; lean_object* v_canon_1917_; lean_object* v_cache_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_st_ref_get(v_a_1910_);
v_canon_1917_ = lean_ctor_get(v___x_1916_, 10);
lean_inc_ref(v_canon_1917_);
lean_dec(v___x_1916_);
v_cache_1918_ = lean_ctor_get(v_canon_1917_, 0);
lean_inc_ref(v_cache_1918_);
lean_dec_ref(v_canon_1917_);
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1918_, v_e_1906_);
lean_dec_ref(v_cache_1918_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v_e_1906_);
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_val_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_object* v___x_1928_; 
lean_dec(v___x_1919_);
lean_inc_ref(v_e_1906_);
v___x_1928_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1906_, v_report_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1968_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1968_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1968_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v_canon_1934_; lean_object* v_share_1935_; lean_object* v_maxFVar_1936_; lean_object* v_proofInstInfo_1937_; lean_object* v_proofInstInfoFVar_1938_; lean_object* v_inferType_1939_; lean_object* v_getLevel_1940_; lean_object* v_congrInfo_1941_; lean_object* v_defEqI_1942_; lean_object* v_extensions_1943_; lean_object* v_issues_1944_; lean_object* v_instanceOverrides_1945_; uint8_t v_debug_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1967_; 
v___x_1933_ = lean_st_ref_take(v_a_1910_);
v_canon_1934_ = lean_ctor_get(v___x_1933_, 10);
v_share_1935_ = lean_ctor_get(v___x_1933_, 0);
v_maxFVar_1936_ = lean_ctor_get(v___x_1933_, 1);
v_proofInstInfo_1937_ = lean_ctor_get(v___x_1933_, 2);
v_proofInstInfoFVar_1938_ = lean_ctor_get(v___x_1933_, 3);
v_inferType_1939_ = lean_ctor_get(v___x_1933_, 4);
v_getLevel_1940_ = lean_ctor_get(v___x_1933_, 5);
v_congrInfo_1941_ = lean_ctor_get(v___x_1933_, 6);
v_defEqI_1942_ = lean_ctor_get(v___x_1933_, 7);
v_extensions_1943_ = lean_ctor_get(v___x_1933_, 8);
v_issues_1944_ = lean_ctor_get(v___x_1933_, 9);
v_instanceOverrides_1945_ = lean_ctor_get(v___x_1933_, 11);
v_debug_1946_ = lean_ctor_get_uint8(v___x_1933_, sizeof(void*)*12);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1948_ = v___x_1933_;
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_instanceOverrides_1945_);
lean_inc(v_canon_1934_);
lean_inc(v_issues_1944_);
lean_inc(v_extensions_1943_);
lean_inc(v_defEqI_1942_);
lean_inc(v_congrInfo_1941_);
lean_inc(v_getLevel_1940_);
lean_inc(v_inferType_1939_);
lean_inc(v_proofInstInfoFVar_1938_);
lean_inc(v_proofInstInfo_1937_);
lean_inc(v_maxFVar_1936_);
lean_inc(v_share_1935_);
lean_dec(v___x_1933_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_cache_1950_; lean_object* v_cacheInType_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1966_; 
v_cache_1950_ = lean_ctor_get(v_canon_1934_, 0);
v_cacheInType_1951_ = lean_ctor_get(v_canon_1934_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_canon_1934_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1953_ = v_canon_1934_;
v_isShared_1954_ = v_isSharedCheck_1966_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_cacheInType_1951_);
lean_inc(v_cache_1950_);
lean_dec(v_canon_1934_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1966_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_inc(v_a_1929_);
v___x_1955_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1950_, v_e_1906_, v_a_1929_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_cacheInType_1951_);
v___x_1957_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 10, v___x_1957_);
v___x_1959_ = v___x_1948_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_share_1935_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_maxFVar_1936_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_proofInstInfo_1937_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_proofInstInfoFVar_1938_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_inferType_1939_);
lean_ctor_set(v_reuseFailAlloc_1964_, 5, v_getLevel_1940_);
lean_ctor_set(v_reuseFailAlloc_1964_, 6, v_congrInfo_1941_);
lean_ctor_set(v_reuseFailAlloc_1964_, 7, v_defEqI_1942_);
lean_ctor_set(v_reuseFailAlloc_1964_, 8, v_extensions_1943_);
lean_ctor_set(v_reuseFailAlloc_1964_, 9, v_issues_1944_);
lean_ctor_set(v_reuseFailAlloc_1964_, 10, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1964_, 11, v_instanceOverrides_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*12, v_debug_1946_);
v___x_1959_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_st_ref_put(v_a_1910_, v___x_1959_);
if (v_isShared_1932_ == 0)
{
v___x_1962_ = v___x_1931_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1929_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1906_);
return v___x_1928_;
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v_canon_1970_; lean_object* v_cacheInType_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_st_ref_get(v_a_1910_);
v_canon_1970_ = lean_ctor_get(v___x_1969_, 10);
lean_inc_ref(v_canon_1970_);
lean_dec(v___x_1969_);
v_cacheInType_1971_ = lean_ctor_get(v_canon_1970_, 1);
lean_inc_ref(v_cacheInType_1971_);
lean_dec_ref(v_canon_1970_);
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1971_, v_e_1906_);
lean_dec_ref(v_cacheInType_1971_);
if (lean_obj_tag(v___x_1972_) == 1)
{
lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_e_1906_);
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
lean_inc_ref(v_e_1906_);
v___x_1981_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1906_, v_report_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2021_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2021_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2021_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v_canon_1987_; lean_object* v_share_1988_; lean_object* v_maxFVar_1989_; lean_object* v_proofInstInfo_1990_; lean_object* v_proofInstInfoFVar_1991_; lean_object* v_inferType_1992_; lean_object* v_getLevel_1993_; lean_object* v_congrInfo_1994_; lean_object* v_defEqI_1995_; lean_object* v_extensions_1996_; lean_object* v_issues_1997_; lean_object* v_instanceOverrides_1998_; uint8_t v_debug_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2020_; 
v___x_1986_ = lean_st_ref_take(v_a_1910_);
v_canon_1987_ = lean_ctor_get(v___x_1986_, 10);
v_share_1988_ = lean_ctor_get(v___x_1986_, 0);
v_maxFVar_1989_ = lean_ctor_get(v___x_1986_, 1);
v_proofInstInfo_1990_ = lean_ctor_get(v___x_1986_, 2);
v_proofInstInfoFVar_1991_ = lean_ctor_get(v___x_1986_, 3);
v_inferType_1992_ = lean_ctor_get(v___x_1986_, 4);
v_getLevel_1993_ = lean_ctor_get(v___x_1986_, 5);
v_congrInfo_1994_ = lean_ctor_get(v___x_1986_, 6);
v_defEqI_1995_ = lean_ctor_get(v___x_1986_, 7);
v_extensions_1996_ = lean_ctor_get(v___x_1986_, 8);
v_issues_1997_ = lean_ctor_get(v___x_1986_, 9);
v_instanceOverrides_1998_ = lean_ctor_get(v___x_1986_, 11);
v_debug_1999_ = lean_ctor_get_uint8(v___x_1986_, sizeof(void*)*12);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2001_ = v___x_1986_;
v_isShared_2002_ = v_isSharedCheck_2020_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_instanceOverrides_1998_);
lean_inc(v_canon_1987_);
lean_inc(v_issues_1997_);
lean_inc(v_extensions_1996_);
lean_inc(v_defEqI_1995_);
lean_inc(v_congrInfo_1994_);
lean_inc(v_getLevel_1993_);
lean_inc(v_inferType_1992_);
lean_inc(v_proofInstInfoFVar_1991_);
lean_inc(v_proofInstInfo_1990_);
lean_inc(v_maxFVar_1989_);
lean_inc(v_share_1988_);
lean_dec(v___x_1986_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2020_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_cache_2003_; lean_object* v_cacheInType_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2019_; 
v_cache_2003_ = lean_ctor_get(v_canon_1987_, 0);
v_cacheInType_2004_ = lean_ctor_get(v_canon_1987_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_canon_1987_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2006_ = v_canon_1987_;
v_isShared_2007_ = v_isSharedCheck_2019_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_cacheInType_2004_);
lean_inc(v_cache_2003_);
lean_dec(v_canon_1987_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2019_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_inc(v_a_1982_);
v___x_2008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2004_, v_e_1906_, v_a_1982_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 10, v___x_2010_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_share_1988_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_maxFVar_1989_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_proofInstInfo_1990_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_proofInstInfoFVar_1991_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_inferType_1992_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_getLevel_1993_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_congrInfo_1994_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_defEqI_1995_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_extensions_1996_);
lean_ctor_set(v_reuseFailAlloc_2017_, 9, v_issues_1997_);
lean_ctor_set(v_reuseFailAlloc_2017_, 10, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 11, v_instanceOverrides_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*12, v_debug_1999_);
v___x_2012_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_st_ref_put(v_a_1910_, v___x_2012_);
if (v_isShared_1985_ == 0)
{
v___x_2015_ = v___x_1984_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_1982_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1906_);
return v___x_1981_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_2038_ = l_Lean_mkConst(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_2039_, lean_object* v_prop_2040_, lean_object* v_inst_2041_, lean_object* v_e_2042_, uint8_t v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2051_; 
lean_inc_ref(v_prop_2040_);
v___x_2051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2040_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2094_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2094_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2094_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___y_2057_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_2052_);
v___x_2063_ = l_Lean_Expr_app___override(v___x_2062_, v_a_2052_);
if (v_a_2043_ == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2063_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___y_2067_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_inc_ref(v_inst_2041_);
v___y_2067_ = v_inst_2041_;
goto v___jp_2066_;
}
else
{
lean_object* v_val_2083_; 
v_val_2083_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2065_, 1);
v___y_2067_ = v_val_2083_;
goto v___jp_2066_;
}
v___jp_2066_:
{
lean_object* v___x_2068_; 
lean_inc_ref(v_inst_2041_);
v___x_2068_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_2041_, v___y_2067_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2082_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
size_t v___x_2073_; size_t v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_ptr_addr(v_prop_2040_);
lean_dec_ref(v_prop_2040_);
v___x_2074_ = lean_ptr_addr(v_a_2052_);
v___x_2075_ = lean_usize_dec_eq(v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_del_object(v___x_2071_);
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_inst_2041_);
v___y_2057_ = v_a_2069_;
goto v___jp_2056_;
}
else
{
size_t v___x_2076_; size_t v___x_2077_; uint8_t v___x_2078_; 
v___x_2076_ = lean_ptr_addr(v_inst_2041_);
lean_dec_ref(v_inst_2041_);
v___x_2077_ = lean_ptr_addr(v_a_2069_);
v___x_2078_ = lean_usize_dec_eq(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_del_object(v___x_2071_);
lean_dec_ref(v_e_2042_);
v___y_2057_ = v_a_2069_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2080_; 
lean_dec(v_a_2069_);
lean_del_object(v___x_2054_);
lean_dec(v_a_2052_);
lean_dec_ref(v_g_2039_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v_e_2042_);
v___x_2080_ = v___x_2071_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_e_2042_);
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
else
{
lean_del_object(v___x_2054_);
lean_dec(v_a_2052_);
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_prop_2040_);
lean_dec_ref(v_g_2039_);
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_del_object(v___x_2054_);
lean_dec(v_a_2052_);
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_prop_2040_);
lean_dec_ref(v_g_2039_);
v_a_2084_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2064_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2064_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
uint8_t v___x_2092_; lean_object* v___x_2093_; 
lean_del_object(v___x_2054_);
lean_dec(v_a_2052_);
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_prop_2040_);
lean_dec_ref(v_g_2039_);
v___x_2092_ = 0;
v___x_2093_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_inst_2041_, v___x_2063_, v___x_2092_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
return v___x_2093_;
}
v___jp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = l_Lean_mkAppB(v_g_2039_, v_a_2052_, v___y_2057_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2058_);
v___x_2060_ = v___x_2054_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_prop_2040_);
lean_dec_ref(v_g_2039_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_2095_, lean_object* v_prop_2096_, lean_object* v_h_2097_, lean_object* v_e_2098_, uint8_t v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
if (v_a_2099_ == 0)
{
lean_object* v___x_2107_; lean_object* v_canon_2108_; lean_object* v_cache_2109_; lean_object* v___x_2110_; 
v___x_2107_ = lean_st_ref_get(v_a_2101_);
v_canon_2108_ = lean_ctor_get(v___x_2107_, 10);
lean_inc_ref(v_canon_2108_);
lean_dec(v___x_2107_);
v_cache_2109_ = lean_ctor_get(v_canon_2108_, 0);
lean_inc_ref(v_cache_2109_);
lean_dec_ref(v_canon_2108_);
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2109_, v_e_2098_);
lean_dec_ref(v_cache_2109_);
if (lean_obj_tag(v___x_2110_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_e_2098_);
lean_dec_ref(v_h_2097_);
lean_dec_ref(v_prop_2096_);
lean_dec_ref(v_g_2095_);
v_val_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 0);
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_val_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v___x_2119_; 
lean_dec(v___x_2110_);
lean_inc_ref(v_e_2098_);
v___x_2119_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2095_, v_prop_2096_, v_h_2097_, v_e_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2159_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2159_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2159_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v_canon_2125_; lean_object* v_share_2126_; lean_object* v_maxFVar_2127_; lean_object* v_proofInstInfo_2128_; lean_object* v_proofInstInfoFVar_2129_; lean_object* v_inferType_2130_; lean_object* v_getLevel_2131_; lean_object* v_congrInfo_2132_; lean_object* v_defEqI_2133_; lean_object* v_extensions_2134_; lean_object* v_issues_2135_; lean_object* v_instanceOverrides_2136_; uint8_t v_debug_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2158_; 
v___x_2124_ = lean_st_ref_take(v_a_2101_);
v_canon_2125_ = lean_ctor_get(v___x_2124_, 10);
v_share_2126_ = lean_ctor_get(v___x_2124_, 0);
v_maxFVar_2127_ = lean_ctor_get(v___x_2124_, 1);
v_proofInstInfo_2128_ = lean_ctor_get(v___x_2124_, 2);
v_proofInstInfoFVar_2129_ = lean_ctor_get(v___x_2124_, 3);
v_inferType_2130_ = lean_ctor_get(v___x_2124_, 4);
v_getLevel_2131_ = lean_ctor_get(v___x_2124_, 5);
v_congrInfo_2132_ = lean_ctor_get(v___x_2124_, 6);
v_defEqI_2133_ = lean_ctor_get(v___x_2124_, 7);
v_extensions_2134_ = lean_ctor_get(v___x_2124_, 8);
v_issues_2135_ = lean_ctor_get(v___x_2124_, 9);
v_instanceOverrides_2136_ = lean_ctor_get(v___x_2124_, 11);
v_debug_2137_ = lean_ctor_get_uint8(v___x_2124_, sizeof(void*)*12);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2139_ = v___x_2124_;
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_instanceOverrides_2136_);
lean_inc(v_canon_2125_);
lean_inc(v_issues_2135_);
lean_inc(v_extensions_2134_);
lean_inc(v_defEqI_2133_);
lean_inc(v_congrInfo_2132_);
lean_inc(v_getLevel_2131_);
lean_inc(v_inferType_2130_);
lean_inc(v_proofInstInfoFVar_2129_);
lean_inc(v_proofInstInfo_2128_);
lean_inc(v_maxFVar_2127_);
lean_inc(v_share_2126_);
lean_dec(v___x_2124_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_cache_2141_; lean_object* v_cacheInType_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2157_; 
v_cache_2141_ = lean_ctor_get(v_canon_2125_, 0);
v_cacheInType_2142_ = lean_ctor_get(v_canon_2125_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_canon_2125_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2144_ = v_canon_2125_;
v_isShared_2145_ = v_isSharedCheck_2157_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_cacheInType_2142_);
lean_inc(v_cache_2141_);
lean_dec(v_canon_2125_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2157_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_inc(v_a_2120_);
v___x_2146_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2141_, v_e_2098_, v_a_2120_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_cacheInType_2142_);
v___x_2148_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 10, v___x_2148_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_share_2126_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_maxFVar_2127_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_proofInstInfo_2128_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_proofInstInfoFVar_2129_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_inferType_2130_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_getLevel_2131_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_congrInfo_2132_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_defEqI_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v_extensions_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 9, v_issues_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 10, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 11, v_instanceOverrides_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*12, v_debug_2137_);
v___x_2150_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_st_ref_put(v_a_2101_, v___x_2150_);
if (v_isShared_2123_ == 0)
{
v___x_2153_ = v___x_2122_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2120_);
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
lean_dec_ref(v_e_2098_);
return v___x_2119_;
}
}
}
else
{
lean_object* v___x_2160_; lean_object* v_canon_2161_; lean_object* v_cacheInType_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_st_ref_get(v_a_2101_);
v_canon_2161_ = lean_ctor_get(v___x_2160_, 10);
lean_inc_ref(v_canon_2161_);
lean_dec(v___x_2160_);
v_cacheInType_2162_ = lean_ctor_get(v_canon_2161_, 1);
lean_inc_ref(v_cacheInType_2162_);
lean_dec_ref(v_canon_2161_);
v___x_2163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2162_, v_e_2098_);
lean_dec_ref(v_cacheInType_2162_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_e_2098_);
lean_dec_ref(v_h_2097_);
lean_dec_ref(v_prop_2096_);
lean_dec_ref(v_g_2095_);
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
lean_inc_ref(v_e_2098_);
v___x_2172_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_2095_, v_prop_2096_, v_h_2097_, v_e_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2212_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2212_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2212_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v_canon_2178_; lean_object* v_share_2179_; lean_object* v_maxFVar_2180_; lean_object* v_proofInstInfo_2181_; lean_object* v_proofInstInfoFVar_2182_; lean_object* v_inferType_2183_; lean_object* v_getLevel_2184_; lean_object* v_congrInfo_2185_; lean_object* v_defEqI_2186_; lean_object* v_extensions_2187_; lean_object* v_issues_2188_; lean_object* v_instanceOverrides_2189_; uint8_t v_debug_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2211_; 
v___x_2177_ = lean_st_ref_take(v_a_2101_);
v_canon_2178_ = lean_ctor_get(v___x_2177_, 10);
v_share_2179_ = lean_ctor_get(v___x_2177_, 0);
v_maxFVar_2180_ = lean_ctor_get(v___x_2177_, 1);
v_proofInstInfo_2181_ = lean_ctor_get(v___x_2177_, 2);
v_proofInstInfoFVar_2182_ = lean_ctor_get(v___x_2177_, 3);
v_inferType_2183_ = lean_ctor_get(v___x_2177_, 4);
v_getLevel_2184_ = lean_ctor_get(v___x_2177_, 5);
v_congrInfo_2185_ = lean_ctor_get(v___x_2177_, 6);
v_defEqI_2186_ = lean_ctor_get(v___x_2177_, 7);
v_extensions_2187_ = lean_ctor_get(v___x_2177_, 8);
v_issues_2188_ = lean_ctor_get(v___x_2177_, 9);
v_instanceOverrides_2189_ = lean_ctor_get(v___x_2177_, 11);
v_debug_2190_ = lean_ctor_get_uint8(v___x_2177_, sizeof(void*)*12);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2192_ = v___x_2177_;
v_isShared_2193_ = v_isSharedCheck_2211_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_instanceOverrides_2189_);
lean_inc(v_canon_2178_);
lean_inc(v_issues_2188_);
lean_inc(v_extensions_2187_);
lean_inc(v_defEqI_2186_);
lean_inc(v_congrInfo_2185_);
lean_inc(v_getLevel_2184_);
lean_inc(v_inferType_2183_);
lean_inc(v_proofInstInfoFVar_2182_);
lean_inc(v_proofInstInfo_2181_);
lean_inc(v_maxFVar_2180_);
lean_inc(v_share_2179_);
lean_dec(v___x_2177_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2211_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v_cache_2194_; lean_object* v_cacheInType_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2210_; 
v_cache_2194_ = lean_ctor_get(v_canon_2178_, 0);
v_cacheInType_2195_ = lean_ctor_get(v_canon_2178_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_canon_2178_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2197_ = v_canon_2178_;
v_isShared_2198_ = v_isSharedCheck_2210_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_cacheInType_2195_);
lean_inc(v_cache_2194_);
lean_dec(v_canon_2178_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2210_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_inc(v_a_2173_);
v___x_2199_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2195_, v_e_2098_, v_a_2173_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 1, v___x_2199_);
v___x_2201_ = v___x_2197_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_cache_2194_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 10, v___x_2201_);
v___x_2203_ = v___x_2192_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_share_2179_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_maxFVar_2180_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_proofInstInfo_2181_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_proofInstInfoFVar_2182_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_inferType_2183_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v_getLevel_2184_);
lean_ctor_set(v_reuseFailAlloc_2208_, 6, v_congrInfo_2185_);
lean_ctor_set(v_reuseFailAlloc_2208_, 7, v_defEqI_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 8, v_extensions_2187_);
lean_ctor_set(v_reuseFailAlloc_2208_, 9, v_issues_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 10, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2208_, 11, v_instanceOverrides_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2208_, sizeof(void*)*12, v_debug_2190_);
v___x_2203_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_st_ref_put(v_a_2101_, v___x_2203_);
if (v_isShared_2176_ == 0)
{
v___x_2206_ = v___x_2175_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2173_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2098_);
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_2213_, lean_object* v_prop_2214_, lean_object* v_h_2215_, lean_object* v_e_2216_, uint8_t v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_a_2226_; 
if (v_a_2217_ == 0)
{
lean_object* v___x_2260_; lean_object* v_canon_2261_; lean_object* v_cache_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_st_ref_get(v_a_2219_);
v_canon_2261_ = lean_ctor_get(v___x_2260_, 10);
lean_inc_ref(v_canon_2261_);
lean_dec(v___x_2260_);
v_cache_2262_ = lean_ctor_get(v_canon_2261_, 0);
lean_inc_ref(v_cache_2262_);
lean_dec_ref(v_canon_2261_);
v___x_2263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2262_, v_e_2216_);
lean_dec_ref(v_cache_2262_);
if (lean_obj_tag(v___x_2263_) == 1)
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v_e_2216_);
lean_dec_ref(v_h_2215_);
lean_dec_ref(v_prop_2214_);
lean_dec_ref(v_g_2213_);
v_val_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_val_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v___x_2272_; 
lean_dec(v___x_2263_);
lean_inc_ref(v_prop_2214_);
v___x_2272_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2214_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc_n(v_a_2273_, 2);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2273_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___y_2277_; lean_object* v___y_2280_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_inc_ref(v_h_2215_);
v___y_2280_ = v_h_2215_;
goto v___jp_2279_;
}
else
{
lean_object* v_val_2287_; 
v_val_2287_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v_a_2275_, 1);
v___y_2280_ = v_val_2287_;
goto v___jp_2279_;
}
v___jp_2276_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_mkAppB(v_g_2213_, v_a_2273_, v___y_2277_);
v_a_2226_ = v___x_2278_;
goto v___jp_2225_;
}
v___jp_2279_:
{
size_t v___x_2281_; size_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = lean_ptr_addr(v_prop_2214_);
lean_dec_ref(v_prop_2214_);
v___x_2282_ = lean_ptr_addr(v_a_2273_);
v___x_2283_ = lean_usize_dec_eq(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_dec_ref(v_h_2215_);
v___y_2277_ = v___y_2280_;
goto v___jp_2276_;
}
else
{
size_t v___x_2284_; size_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2284_ = lean_ptr_addr(v_h_2215_);
lean_dec_ref(v_h_2215_);
v___x_2285_ = lean_ptr_addr(v___y_2280_);
v___x_2286_ = lean_usize_dec_eq(v___x_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
v___y_2277_ = v___y_2280_;
goto v___jp_2276_;
}
else
{
lean_dec_ref(v___y_2280_);
lean_dec(v_a_2273_);
lean_dec_ref(v_g_2213_);
lean_inc_ref(v_e_2216_);
v_a_2226_ = v_e_2216_;
goto v___jp_2225_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2273_);
lean_dec_ref(v_e_2216_);
lean_dec_ref(v_h_2215_);
lean_dec_ref(v_prop_2214_);
lean_dec_ref(v_g_2213_);
v_a_2288_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2274_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2274_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_dec_ref(v_e_2216_);
lean_dec_ref(v_h_2215_);
lean_dec_ref(v_prop_2214_);
lean_dec_ref(v_g_2213_);
return v___x_2272_;
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v_canon_2297_; lean_object* v_cacheInType_2298_; lean_object* v___x_2299_; 
lean_dec_ref(v_g_2213_);
v___x_2296_ = lean_st_ref_get(v_a_2219_);
v_canon_2297_ = lean_ctor_get(v___x_2296_, 10);
lean_inc_ref(v_canon_2297_);
lean_dec(v___x_2296_);
v_cacheInType_2298_ = lean_ctor_get(v_canon_2297_, 1);
lean_inc_ref(v_cacheInType_2298_);
lean_dec_ref(v_canon_2297_);
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2298_, v_e_2216_);
lean_dec_ref(v_cacheInType_2298_);
if (lean_obj_tag(v___x_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_e_2216_);
lean_dec_ref(v_h_2215_);
lean_dec_ref(v_prop_2214_);
v_val_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_val_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set_tag(v___x_2302_, 0);
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_val_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
else
{
lean_object* v___x_2308_; 
lean_dec(v___x_2299_);
v___x_2308_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2214_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = 0;
v___x_2311_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_h_2215_, v_a_2309_, v___x_2310_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2351_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2351_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2351_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v_canon_2317_; lean_object* v_share_2318_; lean_object* v_maxFVar_2319_; lean_object* v_proofInstInfo_2320_; lean_object* v_proofInstInfoFVar_2321_; lean_object* v_inferType_2322_; lean_object* v_getLevel_2323_; lean_object* v_congrInfo_2324_; lean_object* v_defEqI_2325_; lean_object* v_extensions_2326_; lean_object* v_issues_2327_; lean_object* v_instanceOverrides_2328_; uint8_t v_debug_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2350_; 
v___x_2316_ = lean_st_ref_take(v_a_2219_);
v_canon_2317_ = lean_ctor_get(v___x_2316_, 10);
v_share_2318_ = lean_ctor_get(v___x_2316_, 0);
v_maxFVar_2319_ = lean_ctor_get(v___x_2316_, 1);
v_proofInstInfo_2320_ = lean_ctor_get(v___x_2316_, 2);
v_proofInstInfoFVar_2321_ = lean_ctor_get(v___x_2316_, 3);
v_inferType_2322_ = lean_ctor_get(v___x_2316_, 4);
v_getLevel_2323_ = lean_ctor_get(v___x_2316_, 5);
v_congrInfo_2324_ = lean_ctor_get(v___x_2316_, 6);
v_defEqI_2325_ = lean_ctor_get(v___x_2316_, 7);
v_extensions_2326_ = lean_ctor_get(v___x_2316_, 8);
v_issues_2327_ = lean_ctor_get(v___x_2316_, 9);
v_instanceOverrides_2328_ = lean_ctor_get(v___x_2316_, 11);
v_debug_2329_ = lean_ctor_get_uint8(v___x_2316_, sizeof(void*)*12);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2331_ = v___x_2316_;
v_isShared_2332_ = v_isSharedCheck_2350_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_instanceOverrides_2328_);
lean_inc(v_canon_2317_);
lean_inc(v_issues_2327_);
lean_inc(v_extensions_2326_);
lean_inc(v_defEqI_2325_);
lean_inc(v_congrInfo_2324_);
lean_inc(v_getLevel_2323_);
lean_inc(v_inferType_2322_);
lean_inc(v_proofInstInfoFVar_2321_);
lean_inc(v_proofInstInfo_2320_);
lean_inc(v_maxFVar_2319_);
lean_inc(v_share_2318_);
lean_dec(v___x_2316_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2350_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_cache_2333_; lean_object* v_cacheInType_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2349_; 
v_cache_2333_ = lean_ctor_get(v_canon_2317_, 0);
v_cacheInType_2334_ = lean_ctor_get(v_canon_2317_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_canon_2317_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2336_ = v_canon_2317_;
v_isShared_2337_ = v_isSharedCheck_2349_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_cacheInType_2334_);
lean_inc(v_cache_2333_);
lean_dec(v_canon_2317_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2349_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_inc(v_a_2312_);
v___x_2338_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2334_, v_e_2216_, v_a_2312_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_cache_2333_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 10, v___x_2340_);
v___x_2342_ = v___x_2331_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_share_2318_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_maxFVar_2319_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_proofInstInfo_2320_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_proofInstInfoFVar_2321_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_inferType_2322_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_getLevel_2323_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_congrInfo_2324_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_defEqI_2325_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_extensions_2326_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v_issues_2327_);
lean_ctor_set(v_reuseFailAlloc_2347_, 10, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2347_, 11, v_instanceOverrides_2328_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*12, v_debug_2329_);
v___x_2342_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_st_ref_put(v_a_2219_, v___x_2342_);
if (v_isShared_2315_ == 0)
{
v___x_2345_ = v___x_2314_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2312_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2216_);
return v___x_2311_;
}
}
else
{
lean_dec_ref(v_e_2216_);
lean_dec_ref(v_h_2215_);
return v___x_2308_;
}
}
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v_canon_2228_; lean_object* v_share_2229_; lean_object* v_maxFVar_2230_; lean_object* v_proofInstInfo_2231_; lean_object* v_proofInstInfoFVar_2232_; lean_object* v_inferType_2233_; lean_object* v_getLevel_2234_; lean_object* v_congrInfo_2235_; lean_object* v_defEqI_2236_; lean_object* v_extensions_2237_; lean_object* v_issues_2238_; lean_object* v_instanceOverrides_2239_; uint8_t v_debug_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2259_; 
v___x_2227_ = lean_st_ref_take(v_a_2219_);
v_canon_2228_ = lean_ctor_get(v___x_2227_, 10);
v_share_2229_ = lean_ctor_get(v___x_2227_, 0);
v_maxFVar_2230_ = lean_ctor_get(v___x_2227_, 1);
v_proofInstInfo_2231_ = lean_ctor_get(v___x_2227_, 2);
v_proofInstInfoFVar_2232_ = lean_ctor_get(v___x_2227_, 3);
v_inferType_2233_ = lean_ctor_get(v___x_2227_, 4);
v_getLevel_2234_ = lean_ctor_get(v___x_2227_, 5);
v_congrInfo_2235_ = lean_ctor_get(v___x_2227_, 6);
v_defEqI_2236_ = lean_ctor_get(v___x_2227_, 7);
v_extensions_2237_ = lean_ctor_get(v___x_2227_, 8);
v_issues_2238_ = lean_ctor_get(v___x_2227_, 9);
v_instanceOverrides_2239_ = lean_ctor_get(v___x_2227_, 11);
v_debug_2240_ = lean_ctor_get_uint8(v___x_2227_, sizeof(void*)*12);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2242_ = v___x_2227_;
v_isShared_2243_ = v_isSharedCheck_2259_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_instanceOverrides_2239_);
lean_inc(v_canon_2228_);
lean_inc(v_issues_2238_);
lean_inc(v_extensions_2237_);
lean_inc(v_defEqI_2236_);
lean_inc(v_congrInfo_2235_);
lean_inc(v_getLevel_2234_);
lean_inc(v_inferType_2233_);
lean_inc(v_proofInstInfoFVar_2232_);
lean_inc(v_proofInstInfo_2231_);
lean_inc(v_maxFVar_2230_);
lean_inc(v_share_2229_);
lean_dec(v___x_2227_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2259_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_cache_2244_; lean_object* v_cacheInType_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2258_; 
v_cache_2244_ = lean_ctor_get(v_canon_2228_, 0);
v_cacheInType_2245_ = lean_ctor_get(v_canon_2228_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_canon_2228_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2247_ = v_canon_2228_;
v_isShared_2248_ = v_isSharedCheck_2258_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_cacheInType_2245_);
lean_inc(v_cache_2244_);
lean_dec(v_canon_2228_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2258_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_inc_ref(v_a_2226_);
v___x_2249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2244_, v_e_2216_, v_a_2226_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_cacheInType_2245_);
v___x_2251_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 10, v___x_2251_);
v___x_2253_ = v___x_2242_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_share_2229_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_maxFVar_2230_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_proofInstInfo_2231_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_proofInstInfoFVar_2232_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_inferType_2233_);
lean_ctor_set(v_reuseFailAlloc_2256_, 5, v_getLevel_2234_);
lean_ctor_set(v_reuseFailAlloc_2256_, 6, v_congrInfo_2235_);
lean_ctor_set(v_reuseFailAlloc_2256_, 7, v_defEqI_2236_);
lean_ctor_set(v_reuseFailAlloc_2256_, 8, v_extensions_2237_);
lean_ctor_set(v_reuseFailAlloc_2256_, 9, v_issues_2238_);
lean_ctor_set(v_reuseFailAlloc_2256_, 10, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2256_, 11, v_instanceOverrides_2239_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*12, v_debug_2240_);
v___x_2253_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_st_ref_put(v_a_2219_, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_a_2226_);
return v___x_2255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(lean_object* v___x_2352_, lean_object* v_snd_2353_, lean_object* v_a_2354_, uint8_t v___x_2355_, lean_object* v_fst_2356_, lean_object* v_f_2357_, lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v___x_2360_, lean_object* v_____r_2361_, uint8_t v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_arg_x27_2371_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; uint8_t v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___x_2454_; 
lean_inc_ref(v___x_2352_);
v___x_2454_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2360_, v_a_2354_, v___x_2352_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; uint8_t v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
switch(v___x_2456_)
{
case 0:
{
lean_object* v___x_2457_; 
lean_inc_ref(v___x_2352_);
v___x_2457_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2352_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v_arg_x27_2371_ = v_a_2458_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2459_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2457_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2457_);
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
case 1:
{
lean_object* v___x_2467_; 
lean_inc_ref(v___x_2352_);
v___x_2467_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2352_, v___y_2366_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = l_Lean_Expr_cleanupAnnotations(v_a_2468_);
lean_dec(v_a_2468_);
v___x_2470_ = l_Lean_Expr_isApp(v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v___x_2469_);
goto v___jp_2445_;
}
else
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2469_);
v___x_2472_ = l_Lean_Expr_isApp(v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v___x_2471_);
lean_dec_ref(v___x_2469_);
goto v___jp_2445_;
}
else
{
lean_object* v_arg_2473_; lean_object* v_arg_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_arg_2473_ = lean_ctor_get(v___x_2469_, 1);
lean_inc_ref(v_arg_2473_);
lean_dec_ref(v___x_2469_);
v_arg_2474_ = lean_ctor_get(v___x_2471_, 1);
lean_inc_ref(v_arg_2474_);
v___x_2475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2471_);
lean_dec_ref(v___x_2471_);
v___x_2476_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1));
v___x_2477_ = l_Lean_Expr_isConstOf(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2479_ = l_Lean_Expr_isConstOf(v___x_2475_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2473_);
goto v___jp_2445_;
}
else
{
lean_object* v___x_2480_; 
lean_inc_ref(v___x_2352_);
v___x_2480_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2475_, v_arg_2474_, v_arg_2473_, v___x_2352_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v_arg_x27_2371_ = v_a_2481_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2482_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2480_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2480_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
else
{
lean_object* v___x_2490_; 
lean_inc_ref(v___x_2352_);
v___x_2490_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2475_, v_arg_2474_, v_arg_2473_, v___x_2352_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v_arg_x27_2371_ = v_a_2491_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2492_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2490_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2490_);
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
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2500_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2467_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2467_);
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
default: 
{
goto v___jp_2383_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2508_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2454_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2454_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
v___jp_2370_:
{
size_t v___x_2372_; size_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2372_ = lean_ptr_addr(v___x_2352_);
lean_dec_ref(v___x_2352_);
v___x_2373_ = lean_ptr_addr(v_arg_x27_2371_);
v___x_2374_ = lean_usize_dec_eq(v___x_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec(v_fst_2356_);
v___x_2375_ = lean_array_fset(v_snd_2353_, v_a_2354_, v_arg_x27_2371_);
v___x_2376_ = lean_box(v___x_2355_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2375_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_arg_x27_2371_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_fst_2356_);
lean_ctor_set(v___x_2380_, 1, v_snd_2353_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
v___jp_2383_:
{
lean_object* v___x_2384_; 
lean_inc_ref(v___x_2352_);
v___x_2384_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2352_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_arg_x27_2371_ = v_a_2385_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2386_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2384_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2384_);
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
}
v___jp_2394_:
{
lean_object* v___x_2404_; 
lean_inc_ref(v___x_2352_);
v___x_2404_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst(v_f_2357_, v___y_2401_, v___y_2403_, v___x_2352_, v___y_2398_, v___y_2395_, v___y_2396_, v___y_2400_, v___y_2397_, v___y_2402_, v___y_2399_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v_arg_x27_2371_ = v_a_2405_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2406_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2404_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2404_);
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
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_2414_:
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_nat_dec_lt(v___x_2423_, v___x_2358_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = l_outOfBounds___redArg(v___x_2359_);
v___y_2395_ = v___y_2415_;
v___y_2396_ = v___y_2416_;
v___y_2397_ = v___y_2417_;
v___y_2398_ = v___y_2418_;
v___y_2399_ = v___y_2419_;
v___y_2400_ = v___y_2420_;
v___y_2401_ = v___y_2422_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___x_2425_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_array_fget_borrowed(v_snd_2353_, v___x_2423_);
lean_inc(v___x_2426_);
v___y_2395_ = v___y_2415_;
v___y_2396_ = v___y_2416_;
v___y_2397_ = v___y_2417_;
v___y_2398_ = v___y_2418_;
v___y_2399_ = v___y_2419_;
v___y_2400_ = v___y_2420_;
v___y_2401_ = v___y_2422_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___x_2426_;
goto v___jp_2394_;
}
}
v___jp_2427_:
{
lean_object* v___x_2435_; 
lean_inc_ref(v___x_2352_);
v___x_2435_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2352_, v___x_2355_, v___y_2431_, v___y_2428_, v___y_2429_, v___y_2433_, v___y_2430_, v___y_2434_, v___y_2432_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_arg_x27_2371_ = v_a_2436_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_fst_2356_);
lean_dec(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
v___jp_2445_:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = lean_unsigned_to_nat(2u);
v___x_2447_ = lean_nat_dec_eq(v_a_2354_, v___x_2446_);
if (v___x_2447_ == 0)
{
v___y_2428_ = v___y_2363_;
v___y_2429_ = v___y_2364_;
v___y_2430_ = v___y_2366_;
v___y_2431_ = v___y_2362_;
v___y_2432_ = v___y_2368_;
v___y_2433_ = v___y_2365_;
v___y_2434_ = v___y_2367_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v___x_2449_ = l_Lean_Expr_isConstOf(v_f_2357_, v___x_2448_);
if (v___x_2449_ == 0)
{
v___y_2428_ = v___y_2363_;
v___y_2429_ = v___y_2364_;
v___y_2430_ = v___y_2366_;
v___y_2431_ = v___y_2362_;
v___y_2432_ = v___y_2368_;
v___y_2433_ = v___y_2365_;
v___y_2434_ = v___y_2367_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2451_ = lean_nat_dec_lt(v___x_2450_, v___x_2358_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = l_outOfBounds___redArg(v___x_2359_);
v___y_2415_ = v___y_2363_;
v___y_2416_ = v___y_2364_;
v___y_2417_ = v___y_2366_;
v___y_2418_ = v___y_2362_;
v___y_2419_ = v___y_2368_;
v___y_2420_ = v___y_2365_;
v___y_2421_ = v___y_2367_;
v___y_2422_ = v___x_2452_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_array_fget_borrowed(v_snd_2353_, v___x_2450_);
lean_inc(v___x_2453_);
v___y_2415_ = v___y_2363_;
v___y_2416_ = v___y_2364_;
v___y_2417_ = v___y_2366_;
v___y_2418_ = v___y_2362_;
v___y_2419_ = v___y_2368_;
v___y_2420_ = v___y_2365_;
v___y_2421_ = v___y_2367_;
v___y_2422_ = v___x_2453_;
goto v___jp_2414_;
}
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2520_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__1));
v___x_2521_ = l_Lean_Name_append(v___x_2520_, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__3));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__5));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__7));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(lean_object* v_upperBound_2531_, lean_object* v___x_2532_, lean_object* v_f_2533_, lean_object* v___x_2534_, lean_object* v_a_2535_, lean_object* v_b_2536_, uint8_t v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___y_2546_; uint8_t v___x_2568_; 
v___x_2568_ = lean_nat_dec_lt(v_a_2535_, v_upperBound_2531_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_dec(v_a_2535_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_b_2536_);
return v___x_2569_;
}
else
{
lean_object* v_toCold_2570_; lean_object* v_options_2571_; lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2638_; 
v_toCold_2570_ = lean_ctor_get(v___y_2542_, 0);
v_options_2571_ = lean_ctor_get(v_toCold_2570_, 2);
v_fst_2572_ = lean_ctor_get(v_b_2536_, 0);
v_snd_2573_ = lean_ctor_get(v_b_2536_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_b_2536_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2575_ = v_b_2536_;
v_isShared_2576_ = v_isSharedCheck_2638_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_snd_2573_);
lean_inc(v_fst_2572_);
lean_dec(v_b_2536_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2638_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_inheritedTraceOptions_2577_; uint8_t v_hasTrace_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_inheritedTraceOptions_2577_ = lean_ctor_get(v_toCold_2570_, 11);
v_hasTrace_2578_ = lean_ctor_get_uint8(v_options_2571_, sizeof(void*)*1);
v___x_2579_ = l_Lean_instInhabitedExpr;
v___x_2580_ = lean_array_fget(v_snd_2573_, v_a_2535_);
if (v_hasTrace_2578_ == 0)
{
lean_del_object(v___x_2575_);
goto v___jp_2581_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__2);
v___x_2586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2577_, v_options_2571_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_del_object(v___x_2575_);
goto v___jp_2581_;
}
else
{
lean_object* v___x_2587_; 
lean_inc(v___x_2580_);
v___x_2587_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2534_, v_a_2535_, v___x_2580_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
lean_inc(v___y_2543_);
lean_inc_ref(v___y_2542_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___x_2580_);
v___x_2589_ = lean_infer_type(v___x_2580_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___y_2593_; uint8_t v___x_2617_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__4);
v___x_2617_ = lean_unbox(v_a_2588_);
lean_dec(v_a_2588_);
switch(v___x_2617_)
{
case 0:
{
lean_object* v___x_2618_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2593_ = v___x_2618_;
goto v___jp_2592_;
}
case 1:
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2593_ = v___x_2619_;
goto v___jp_2592_;
}
case 2:
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2593_ = v___x_2620_;
goto v___jp_2592_;
}
default: 
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2593_ = v___x_2621_;
goto v___jp_2592_;
}
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_inc(v___y_2593_);
v___x_2594_ = l_Lean_MessageData_ofFormat(v___y_2593_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 7);
lean_ctor_set(v___x_2575_, 1, v___x_2594_);
lean_ctor_set(v___x_2575_, 0, v___x_2591_);
v___x_2596_ = v___x_2575_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__6);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_inc(v___x_2580_);
v___x_2599_ = l_Lean_MessageData_ofExpr(v___x_2580_);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___closed__8);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_MessageData_ofExpr(v_a_2590_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v___x_2584_, v___x_2604_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2580_, v_snd_2573_, v_a_2535_, v___x_2568_, v_fst_2572_, v_f_2533_, v___x_2532_, v___x_2579_, v___x_2534_, v_a_2606_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
v___y_2546_ = v___x_2607_;
goto v___jp_2545_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v___x_2580_);
lean_dec(v_snd_2573_);
lean_dec(v_fst_2572_);
lean_dec(v_a_2535_);
v_a_2608_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2605_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2605_);
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
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2588_);
lean_dec(v___x_2580_);
lean_del_object(v___x_2575_);
lean_dec(v_snd_2573_);
lean_dec(v_fst_2572_);
lean_dec(v_a_2535_);
v_a_2622_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2589_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2589_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v___x_2580_);
lean_del_object(v___x_2575_);
lean_dec(v_snd_2573_);
lean_dec(v_fst_2572_);
lean_dec(v_a_2535_);
v_a_2630_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2587_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2587_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
v___jp_2581_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_2580_, v_snd_2573_, v_a_2535_, v___x_2568_, v_fst_2572_, v_f_2533_, v___x_2532_, v___x_2579_, v___x_2534_, v___x_2582_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
v___y_2546_ = v___x_2583_;
goto v___jp_2545_;
}
}
}
v___jp_2545_:
{
if (lean_obj_tag(v___y_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2559_; 
v_a_2547_ = lean_ctor_get(v___y_2546_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___y_2546_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2549_ = v___y_2546_;
v_isShared_2550_ = v_isSharedCheck_2559_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___y_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2559_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
if (lean_obj_tag(v_a_2547_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; 
lean_dec(v_a_2535_);
v_a_2551_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v_a_2547_, 1);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_a_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_del_object(v___x_2549_);
v_a_2555_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2556_ = lean_unsigned_to_nat(1u);
v___x_2557_ = lean_nat_add(v_a_2535_, v___x_2556_);
lean_dec(v_a_2535_);
v_a_2535_ = v___x_2557_;
v_b_2536_ = v_a_2555_;
goto _start;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2535_);
v_a_2560_ = lean_ctor_get(v___y_2546_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___y_2546_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___y_2546_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___y_2546_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(lean_object* v_e_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, uint8_t v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___y_2652_; uint8_t v_modified_2653_; lean_object* v_f_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v_args_2710_; uint8_t v_modified_2711_; uint8_t v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; uint8_t v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; 
if (lean_obj_tag(v_x_2640_) == 5)
{
lean_object* v_fn_2747_; lean_object* v_arg_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_fn_2747_ = lean_ctor_get(v_x_2640_, 0);
lean_inc_ref(v_fn_2747_);
v_arg_2748_ = lean_ctor_get(v_x_2640_, 1);
lean_inc_ref(v_arg_2748_);
lean_dec_ref_known(v_x_2640_, 2);
v___x_2749_ = lean_array_set(v_x_2641_, v_x_2642_, v_arg_2748_);
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = lean_nat_sub(v_x_2642_, v___x_2750_);
lean_dec(v_x_2642_);
v_x_2640_ = v_fn_2747_;
v_x_2641_ = v___x_2749_;
v_x_2642_ = v___x_2751_;
goto _start;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
lean_dec(v_x_2642_);
v___x_2753_ = lean_array_get_size(v_x_2641_);
v___x_2754_ = lean_unsigned_to_nat(2u);
v___x_2755_ = lean_nat_dec_eq(v___x_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
v___y_2726_ = v___y_2643_;
v___y_2727_ = v___y_2644_;
v___y_2728_ = v___y_2645_;
v___y_2729_ = v___y_2646_;
v___y_2730_ = v___y_2647_;
v___y_2731_ = v___y_2648_;
v___y_2732_ = v___y_2649_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2756_ = l_Lean_instInhabitedExpr;
v___x_2757_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___closed__1));
v___x_2758_ = l_Lean_Expr_isConstOf(v_x_2640_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2760_ = l_Lean_Expr_isConstOf(v_x_2640_, v___x_2759_);
if (v___x_2760_ == 0)
{
v___y_2726_ = v___y_2643_;
v___y_2727_ = v___y_2644_;
v___y_2728_ = v___y_2645_;
v___y_2729_ = v___y_2646_;
v___y_2730_ = v___y_2647_;
v___y_2731_ = v___y_2648_;
v___y_2732_ = v___y_2649_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = lean_array_get(v___x_2756_, v_x_2641_, v___x_2761_);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_array_get(v___x_2756_, v_x_2641_, v___x_2763_);
lean_dec_ref(v_x_2641_);
v___x_2765_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2640_, v___x_2762_, v___x_2764_, v_e_2639_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2765_;
}
}
else
{
lean_object* v___x_2766_; lean_object* v_prop_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_unsigned_to_nat(0u);
v_prop_2767_ = lean_array_get_borrowed(v___x_2756_, v_x_2641_, v___x_2766_);
lean_inc(v_prop_2767_);
v___x_2768_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2767_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2785_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
size_t v___x_2773_; size_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = lean_ptr_addr(v_prop_2767_);
v___x_2774_ = lean_ptr_addr(v_a_2769_);
v___x_2775_ = lean_usize_dec_eq(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_dec_ref(v_e_2639_);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_array_get(v___x_2756_, v_x_2641_, v___x_2776_);
lean_dec_ref(v_x_2641_);
v___x_2778_ = l_Lean_mkAppB(v_x_2640_, v_a_2769_, v___x_2777_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2778_);
v___x_2780_ = v___x_2771_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
else
{
lean_object* v___x_2783_; 
lean_dec(v_a_2769_);
lean_dec_ref(v_x_2641_);
lean_dec_ref(v_x_2640_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v_e_2639_);
v___x_2783_ = v___x_2771_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_e_2639_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_dec_ref(v_x_2641_);
lean_dec_ref(v_x_2640_);
lean_dec_ref(v_e_2639_);
return v___x_2768_;
}
}
}
}
v___jp_2651_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_box(0);
lean_inc_ref(v_f_2654_);
v___x_2663_ = l_Lean_Meta_getFunInfo(v_f_2654_, v___x_2662_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_paramInfo_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2699_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v_paramInfo_2665_ = lean_ctor_get(v_a_2664_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v_a_2664_, 1);
lean_dec(v_unused_2700_);
v___x_2667_ = v_a_2664_;
v_isShared_2668_ = v_isSharedCheck_2699_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_paramInfo_2665_);
lean_dec(v_a_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2699_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2669_ = lean_array_get_size(v___y_2652_);
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = lean_box(v_modified_2653_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___y_2652_);
lean_ctor_set(v___x_2667_, 0, v___x_2671_);
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___y_2652_);
v___x_2673_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v___x_2669_, v___x_2669_, v_f_2654_, v_paramInfo_2665_, v___x_2670_, v___x_2673_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec_ref(v_paramInfo_2665_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2689_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_fst_2679_; uint8_t v___x_2680_; 
v_fst_2679_ = lean_ctor_get(v_a_2675_, 0);
v___x_2680_ = lean_unbox(v_fst_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2682_; 
lean_dec(v_a_2675_);
lean_dec_ref(v_f_2654_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v_e_2639_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_e_2639_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v_snd_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_dec_ref(v_e_2639_);
v_snd_2684_ = lean_ctor_get(v_a_2675_, 1);
lean_inc(v_snd_2684_);
lean_dec(v_a_2675_);
v___x_2685_ = l_Lean_mkAppN(v_f_2654_, v_snd_2684_);
lean_dec(v_snd_2684_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2685_);
v___x_2687_ = v___x_2677_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v_f_2654_);
lean_dec_ref(v_e_2639_);
v_a_2690_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2674_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2674_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_f_2654_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_e_2639_);
v_a_2701_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2663_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2663_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
v___jp_2709_:
{
lean_object* v___x_2719_; 
lean_inc_ref(v_x_2640_);
v___x_2719_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2640_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; size_t v___x_2721_; size_t v___x_2722_; uint8_t v___x_2723_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = lean_ptr_addr(v_x_2640_);
v___x_2722_ = lean_ptr_addr(v_a_2720_);
v___x_2723_ = lean_usize_dec_eq(v___x_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
uint8_t v___x_2724_; 
lean_dec_ref(v_x_2640_);
v___x_2724_ = 1;
v___y_2652_ = v_args_2710_;
v_modified_2653_ = v___x_2724_;
v_f_2654_ = v_a_2720_;
v___y_2655_ = v___y_2712_;
v___y_2656_ = v___y_2713_;
v___y_2657_ = v___y_2714_;
v___y_2658_ = v___y_2715_;
v___y_2659_ = v___y_2716_;
v___y_2660_ = v___y_2717_;
v___y_2661_ = v___y_2718_;
goto v___jp_2651_;
}
else
{
lean_dec(v_a_2720_);
v___y_2652_ = v_args_2710_;
v_modified_2653_ = v_modified_2711_;
v_f_2654_ = v_x_2640_;
v___y_2655_ = v___y_2712_;
v___y_2656_ = v___y_2713_;
v___y_2657_ = v___y_2714_;
v___y_2658_ = v___y_2715_;
v___y_2659_ = v___y_2716_;
v___y_2660_ = v___y_2717_;
v___y_2661_ = v___y_2718_;
goto v___jp_2651_;
}
}
else
{
lean_dec_ref(v_args_2710_);
lean_dec_ref(v_x_2640_);
lean_dec_ref(v_e_2639_);
return v___x_2719_;
}
}
v___jp_2725_:
{
uint8_t v_modified_2733_; lean_object* v___x_2734_; uint8_t v_modified_2735_; 
v_modified_2733_ = 0;
v___x_2734_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v_modified_2735_ = l_Lean_Expr_isConstOf(v_x_2640_, v___x_2734_);
if (v_modified_2735_ == 0)
{
v_args_2710_ = v_x_2641_;
v_modified_2711_ = v_modified_2733_;
v___y_2712_ = v___y_2726_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2728_;
v___y_2715_ = v___y_2729_;
v___y_2716_ = v___y_2730_;
v___y_2717_ = v___y_2731_;
v___y_2718_ = v___y_2732_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2736_; 
lean_inc_ref(v_x_2641_);
v___x_2736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___redArg(v_x_2641_, v___y_2730_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
if (lean_obj_tag(v_a_2737_) == 1)
{
lean_object* v_val_2738_; 
lean_dec_ref(v_x_2641_);
v_val_2738_ = lean_ctor_get(v_a_2737_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v_a_2737_, 1);
v_args_2710_ = v_val_2738_;
v_modified_2711_ = v_modified_2735_;
v___y_2712_ = v___y_2726_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2728_;
v___y_2715_ = v___y_2729_;
v___y_2716_ = v___y_2730_;
v___y_2717_ = v___y_2731_;
v___y_2718_ = v___y_2732_;
goto v___jp_2709_;
}
else
{
lean_dec(v_a_2737_);
v_args_2710_ = v_x_2641_;
v_modified_2711_ = v_modified_2733_;
v___y_2712_ = v___y_2726_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2728_;
v___y_2715_ = v___y_2729_;
v___y_2716_ = v___y_2730_;
v___y_2717_ = v___y_2731_;
v___y_2718_ = v___y_2732_;
goto v___jp_2709_;
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec_ref(v_x_2641_);
lean_dec_ref(v_x_2640_);
lean_dec_ref(v_e_2639_);
v_a_2739_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2736_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2736_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2786_, uint8_t v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_dummy_2795_; lean_object* v_nargs_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_dummy_2795_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2796_ = l_Lean_Expr_getAppNumArgs(v_e_2786_);
lean_inc(v_nargs_2796_);
v___x_2797_ = lean_mk_array(v_nargs_2796_, v_dummy_2795_);
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_sub(v_nargs_2796_, v___x_2798_);
lean_dec(v_nargs_2796_);
lean_inc_ref(v_e_2786_);
v___x_2800_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_2786_, v_e_2786_, v___x_2797_, v___x_2799_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_2801_, uint8_t v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v___x_2830_; 
v___x_2830_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_2801_);
if (v___x_2830_ == 0)
{
lean_object* v_f_2831_; 
v_f_2831_ = l_Lean_Expr_getAppFn(v_e_2801_);
if (lean_obj_tag(v_f_2831_) == 4)
{
lean_object* v_declName_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_declName_2832_ = lean_ctor_get(v_f_2831_, 0);
lean_inc(v_declName_2832_);
lean_dec_ref_known(v_f_2831_, 2);
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__2));
v___x_2834_ = lean_name_eq(v_declName_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__6));
v___x_2836_ = lean_name_eq(v_declName_2832_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__4));
v___x_2838_ = lean_name_eq(v_declName_2832_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_getNestedNatValue_x3f___closed__2));
v___x_2840_ = lean_name_eq(v_declName_2832_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Meta_Sym_Canon_normNumLit_x3f___closed__1));
v___x_2842_ = lean_name_eq(v_declName_2832_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_2832_, v_a_2808_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2873_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2873_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2873_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 1)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; 
lean_del_object(v___x_2846_);
v_val_2848_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v_a_2844_, 1);
lean_inc_ref(v_e_2801_);
v___x_2849_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_2848_, v_e_2801_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_val_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2861_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v_e_2801_);
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_e_2801_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v_val_2857_; lean_object* v___x_2859_; 
lean_dec_ref(v_e_2801_);
v_val_2857_ = lean_ctor_get(v_a_2850_, 0);
lean_inc(v_val_2857_);
lean_dec_ref_known(v_a_2850_, 1);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v_val_2857_);
v___x_2859_ = v___x_2852_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_val_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_e_2801_);
v_a_2862_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2849_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2849_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_a_2844_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_e_2801_);
v___x_2871_ = v___x_2846_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_e_2801_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v_e_2801_);
v_a_2874_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2843_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2843_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_dec(v_declName_2832_);
goto v___jp_2810_;
}
}
else
{
lean_dec(v_declName_2832_);
goto v___jp_2810_;
}
}
else
{
lean_dec(v_declName_2832_);
goto v___jp_2810_;
}
}
else
{
lean_dec(v_declName_2832_);
goto v___jp_2810_;
}
}
else
{
lean_dec(v_declName_2832_);
goto v___jp_2810_;
}
}
else
{
lean_object* v___x_2882_; 
lean_dec_ref(v_f_2831_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_e_2801_);
return v___x_2882_;
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref(v_e_2801_);
v___x_2883_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed), 8, 1);
lean_closure_set(v___x_2883_, 0, v_e_2801_);
v___x_2884_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_2883_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2918_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2918_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2918_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v_val_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_dec_ref(v_e_2801_);
v_val_2889_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_val_2889_);
lean_dec_ref_known(v_a_2885_, 1);
v___x_2890_ = l_Lean_mkNatLit(v_val_2889_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2890_);
v___x_2892_ = v___x_2887_;
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
else
{
lean_object* v___x_2894_; 
lean_del_object(v___x_2887_);
lean_dec(v_a_2885_);
lean_inc_ref(v_e_2801_);
v___x_2894_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_2801_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2909_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
if (lean_obj_tag(v_a_2895_) == 1)
{
lean_object* v_val_2899_; lean_object* v_fst_2900_; lean_object* v_snd_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_dec_ref(v_e_2801_);
v_val_2899_ = lean_ctor_get(v_a_2895_, 0);
lean_inc(v_val_2899_);
lean_dec_ref_known(v_a_2895_, 1);
v_fst_2900_ = lean_ctor_get(v_val_2899_, 0);
lean_inc(v_fst_2900_);
v_snd_2901_ = lean_ctor_get(v_val_2899_, 1);
lean_inc(v_snd_2901_);
lean_dec(v_val_2899_);
v___x_2902_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_mkOffset(v_fst_2900_, v_snd_2901_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2902_);
v___x_2904_ = v___x_2897_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
else
{
lean_object* v___x_2907_; 
lean_dec(v_a_2895_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_e_2801_);
v___x_2907_ = v___x_2897_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_e_2801_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_e_2801_);
v_a_2910_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2894_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2894_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_e_2801_);
v_a_2919_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2884_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2884_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
v___jp_2810_:
{
lean_object* v___x_2811_; 
lean_inc_ref(v_e_2801_);
v___x_2811_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_e_2801_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2821_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 1)
{
lean_object* v_val_2816_; lean_object* v___x_2817_; 
lean_del_object(v___x_2814_);
lean_dec_ref(v_e_2801_);
v_val_2816_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v_a_2812_, 1);
v___x_2817_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2816_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2817_;
}
else
{
lean_object* v___x_2819_; 
lean_dec(v_a_2812_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_e_2801_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_e_2801_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v_e_2801_);
v_a_2822_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2811_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2811_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2927_, uint8_t v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2937_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
return v___x_2938_;
}
else
{
return v___x_2936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2939_, uint8_t v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2939_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
if (lean_obj_tag(v_a_2949_) == 0)
{
lean_object* v_val_2950_; lean_object* v___x_2951_; 
lean_dec_ref(v_e_2939_);
v_val_2950_ = lean_ctor_get(v_a_2949_, 0);
lean_inc_ref(v_val_2950_);
lean_dec_ref_known(v_a_2949_, 1);
v___x_2951_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2950_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; 
lean_dec(v_a_2949_);
v___x_2952_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2953_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2964_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2964_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2964_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
if (lean_obj_tag(v_a_2955_) == 0)
{
lean_object* v_val_2959_; lean_object* v___x_2960_; 
lean_del_object(v___x_2957_);
lean_dec(v_a_2953_);
v_val_2959_ = lean_ctor_get(v_a_2955_, 0);
lean_inc_ref(v_val_2959_);
lean_dec_ref_known(v_a_2955_, 1);
v___x_2960_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2959_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
return v___x_2960_;
}
else
{
lean_object* v___x_2962_; 
lean_dec(v_a_2955_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v_a_2953_);
v___x_2962_ = v___x_2957_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2953_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_a_2953_);
v_a_2965_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2954_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2954_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
return v___x_2952_;
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_e_2939_);
v_a_2973_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2948_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2948_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2987_, uint8_t v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
uint8_t v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___x_3006_; 
lean_inc_ref(v_e_2987_);
v___x_3006_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2987_, v_a_2992_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_Expr_cleanupAnnotations(v_a_3007_);
lean_dec(v_a_3007_);
v___x_3009_ = l_Lean_Expr_isApp(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v___x_3008_);
v___y_2997_ = v_a_2988_;
v___y_2998_ = v_a_2989_;
v___y_2999_ = v_a_2990_;
v___y_3000_ = v_a_2991_;
v___y_3001_ = v_a_2992_;
v___y_3002_ = v_a_2993_;
v___y_3003_ = v_a_2994_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3008_);
v___x_3011_ = l_Lean_Expr_isApp(v___x_3010_);
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3010_);
lean_dec_ref(v___x_3008_);
v___y_2997_ = v_a_2988_;
v___y_2998_ = v_a_2989_;
v___y_2999_ = v_a_2990_;
v___y_3000_ = v_a_2991_;
v___y_3001_ = v_a_2992_;
v___y_3002_ = v_a_2993_;
v___y_3003_ = v_a_2994_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3010_);
v___x_3013_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_3014_ = l_Lean_Expr_isConstOf(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec_ref(v___x_3012_);
lean_dec_ref(v___x_3010_);
lean_dec_ref(v___x_3008_);
v___y_2997_ = v_a_2988_;
v___y_2998_ = v_a_2989_;
v___y_2999_ = v_a_2990_;
v___y_3000_ = v_a_2991_;
v___y_3001_ = v_a_2992_;
v___y_3002_ = v_a_2993_;
v___y_3003_ = v_a_2994_;
goto v___jp_2996_;
}
else
{
lean_object* v_arg_3015_; lean_object* v_arg_3016_; lean_object* v___x_3017_; 
v_arg_3015_ = lean_ctor_get(v___x_3008_, 1);
lean_inc_ref(v_arg_3015_);
lean_dec_ref(v___x_3008_);
v_arg_3016_ = lean_ctor_get(v___x_3010_, 1);
lean_inc_ref(v_arg_3016_);
lean_dec_ref(v___x_3010_);
v___x_3017_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_3012_, v_arg_3016_, v_arg_3015_, v_e_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
return v___x_3017_;
}
}
}
}
else
{
lean_dec_ref(v_e_2987_);
return v___x_3006_;
}
v___jp_2996_:
{
uint8_t v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = 0;
v___x_3005_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2987_, v___x_3004_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_3018_, lean_object* v_00_u03b1_3019_, lean_object* v_c_3020_, lean_object* v_inst_3021_, lean_object* v_a_3022_, lean_object* v_b_3023_, uint8_t v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_3020_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_3033_);
if (v___x_3034_ == 0)
{
uint8_t v___x_3035_; 
v___x_3035_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_3033_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_3019_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3038_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
v___x_3038_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_3021_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3022_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l_Lean_mkApp5(v_f_3018_, v_a_3037_, v_a_3033_, v_a_3039_, v_a_3041_, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_dec(v_a_3041_);
lean_dec(v_a_3039_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec_ref(v_f_3018_);
return v___x_3042_;
}
}
else
{
lean_dec(v_a_3039_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec_ref(v_b_3023_);
lean_dec_ref(v_f_3018_);
return v___x_3040_;
}
}
else
{
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec_ref(v_b_3023_);
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_f_3018_);
return v___x_3038_;
}
}
else
{
lean_dec(v_a_3033_);
lean_dec_ref(v_b_3023_);
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_inst_3021_);
lean_dec_ref(v_f_3018_);
return v___x_3036_;
}
}
else
{
lean_object* v___x_3052_; 
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_inst_3021_);
lean_dec_ref(v_00_u03b1_3019_);
lean_dec_ref(v_f_3018_);
v___x_3052_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
return v___x_3052_;
}
}
else
{
lean_object* v___x_3053_; 
lean_dec(v_a_3033_);
lean_dec_ref(v_b_3023_);
lean_dec_ref(v_inst_3021_);
lean_dec_ref(v_00_u03b1_3019_);
lean_dec_ref(v_f_3018_);
v___x_3053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3022_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
return v___x_3053_;
}
}
else
{
lean_dec_ref(v_b_3023_);
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_inst_3021_);
lean_dec_ref(v_00_u03b1_3019_);
lean_dec_ref(v_f_3018_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_3054_, lean_object* v_00_u03b1_3055_, lean_object* v_c_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, uint8_t v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_3056_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; uint8_t v___x_3069_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = l_Lean_Expr_isBoolTrue(v_a_3068_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
v___x_3070_ = l_Lean_Expr_isBoolFalse(v_a_3068_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_3055_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3057_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_Lean_mkApp4(v_f_3054_, v_a_3072_, v_a_3068_, v_a_3074_, v_a_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3068_);
lean_dec_ref(v_f_3054_);
return v___x_3075_;
}
}
else
{
lean_dec(v_a_3072_);
lean_dec(v_a_3068_);
lean_dec_ref(v_b_3058_);
lean_dec_ref(v_f_3054_);
return v___x_3073_;
}
}
else
{
lean_dec(v_a_3068_);
lean_dec_ref(v_b_3058_);
lean_dec_ref(v_a_3057_);
lean_dec_ref(v_f_3054_);
return v___x_3071_;
}
}
else
{
lean_object* v___x_3085_; 
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3057_);
lean_dec_ref(v_00_u03b1_3055_);
lean_dec_ref(v_f_3054_);
v___x_3085_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3085_;
}
}
else
{
lean_object* v___x_3086_; 
lean_dec(v_a_3068_);
lean_dec_ref(v_b_3058_);
lean_dec_ref(v_00_u03b1_3055_);
lean_dec_ref(v_f_3054_);
v___x_3086_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_3057_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3086_;
}
}
else
{
lean_dec_ref(v_b_3058_);
lean_dec_ref(v_a_3057_);
lean_dec_ref(v_00_u03b1_3055_);
lean_dec_ref(v_f_3054_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_3087_, uint8_t v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; uint8_t v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___x_3132_; 
lean_inc_ref(v_e_3087_);
v___x_3132_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3087_, v_a_3092_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = l_Lean_Expr_cleanupAnnotations(v_a_3133_);
lean_dec(v_a_3133_);
v___x_3135_ = l_Lean_Expr_isApp(v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec_ref(v___x_3134_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3134_);
v___x_3137_ = l_Lean_Expr_isApp(v___x_3136_);
if (v___x_3137_ == 0)
{
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___x_3134_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3136_);
v___x_3139_ = l_Lean_Expr_isApp(v___x_3138_);
if (v___x_3139_ == 0)
{
lean_dec_ref(v___x_3138_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___x_3134_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3138_);
v___x_3141_ = l_Lean_Expr_isApp(v___x_3140_);
if (v___x_3141_ == 0)
{
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3138_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___x_3134_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v_arg_3142_; lean_object* v_arg_3143_; lean_object* v_arg_3144_; lean_object* v_arg_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_arg_3142_ = lean_ctor_get(v___x_3134_, 1);
lean_inc_ref(v_arg_3142_);
lean_dec_ref(v___x_3134_);
v_arg_3143_ = lean_ctor_get(v___x_3136_, 1);
lean_inc_ref(v_arg_3143_);
lean_dec_ref(v___x_3136_);
v_arg_3144_ = lean_ctor_get(v___x_3138_, 1);
lean_inc_ref(v_arg_3144_);
lean_dec_ref(v___x_3138_);
v_arg_3145_ = lean_ctor_get(v___x_3140_, 1);
lean_inc_ref(v_arg_3145_);
v___x_3146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3140_);
lean_dec_ref(v___x_3140_);
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_3148_ = l_Lean_Expr_isConstOf(v___x_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
uint8_t v___x_3149_; 
v___x_3149_ = l_Lean_Expr_isApp(v___x_3146_);
if (v___x_3149_ == 0)
{
lean_dec_ref(v___x_3146_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3144_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3142_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3146_);
v___x_3151_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_3152_ = l_Lean_Expr_isConstOf(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_dec_ref(v___x_3150_);
lean_dec_ref(v___x_3146_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3144_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3142_);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v___y_3127_ = v_a_3094_;
goto v___jp_3120_;
}
else
{
lean_object* v_arg_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v_e_3087_);
v_arg_3153_ = lean_ctor_get(v___x_3146_, 1);
lean_inc_ref(v_arg_3153_);
lean_dec_ref(v___x_3146_);
v___x_3154_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_3150_, v_arg_3153_, v_arg_3145_, v_arg_3144_, v_arg_3143_, v_arg_3142_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
return v___x_3154_;
}
}
}
else
{
lean_object* v___x_3155_; 
lean_dec_ref(v_e_3087_);
v___x_3155_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_3146_, v_arg_3145_, v_arg_3144_, v_arg_3143_, v_arg_3142_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
return v___x_3155_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_3087_);
return v___x_3132_;
}
v___jp_3096_:
{
if (lean_obj_tag(v___y_3104_) == 4)
{
lean_object* v_declName_3105_; lean_object* v___x_3106_; 
v_declName_3105_ = lean_ctor_get(v___y_3104_, 0);
lean_inc(v_declName_3105_);
lean_dec_ref_known(v___y_3104_, 2);
v___x_3106_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3105_, v___y_3098_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; uint8_t v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = lean_unbox(v_a_3107_);
lean_dec(v_a_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3087_, v___y_3100_, v___y_3101_, v___y_3103_, v___y_3097_, v___y_3102_, v___y_3099_, v___y_3098_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3087_, v___y_3100_, v___y_3101_, v___y_3103_, v___y_3097_, v___y_3102_, v___y_3099_, v___y_3098_);
return v___x_3110_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v_e_3087_);
v_a_3111_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3106_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3106_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v___x_3119_; 
lean_dec_ref(v___y_3104_);
v___x_3119_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3087_, v___y_3100_, v___y_3101_, v___y_3103_, v___y_3097_, v___y_3102_, v___y_3099_, v___y_3098_);
return v___x_3119_;
}
}
v___jp_3120_:
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = l_Lean_Expr_getAppFn(v_e_3087_);
v___x_3129_ = l_Lean_Expr_isLambda(v___x_3128_);
if (v___x_3129_ == 0)
{
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3127_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3121_;
v___y_3101_ = v___y_3122_;
v___y_3102_ = v___y_3125_;
v___y_3103_ = v___y_3123_;
v___y_3104_ = v___x_3128_;
goto v___jp_3096_;
}
else
{
if (v___y_3121_ == 0)
{
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3127_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3121_;
v___y_3101_ = v___y_3122_;
v___y_3102_ = v___y_3125_;
v___y_3103_ = v___y_3123_;
v___y_3104_ = v___x_3128_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec_ref(v___x_3128_);
v___x_3130_ = l_Lean_Expr_headBeta(v_e_3087_);
v___x_3131_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3130_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3131_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_3160_ = lean_unsigned_to_nat(18u);
v___x_3161_ = lean_unsigned_to_nat(1955u);
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_3163_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_3164_ = l_mkPanicMessageWithDecl(v___x_3163_, v___x_3162_, v___x_3161_, v___x_3160_, v___x_3159_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_3165_, uint8_t v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = l_Lean_Expr_projExpr_x21(v_e_3165_);
v___x_3175_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_3174_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___y_3178_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3175_, 1);
if (lean_obj_tag(v_e_3165_) == 11)
{
lean_object* v_typeName_3200_; lean_object* v_idx_3201_; lean_object* v_struct_3202_; size_t v___x_3203_; size_t v___x_3204_; uint8_t v___x_3205_; 
v_typeName_3200_ = lean_ctor_get(v_e_3165_, 0);
v_idx_3201_ = lean_ctor_get(v_e_3165_, 1);
v_struct_3202_ = lean_ctor_get(v_e_3165_, 2);
v___x_3203_ = lean_ptr_addr(v_struct_3202_);
v___x_3204_ = lean_ptr_addr(v_a_3176_);
v___x_3205_ = lean_usize_dec_eq(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_inc(v_idx_3201_);
lean_inc(v_typeName_3200_);
lean_dec_ref_known(v_e_3165_, 3);
v___x_3206_ = l_Lean_Expr_proj___override(v_typeName_3200_, v_idx_3201_, v_a_3176_);
v___y_3178_ = v___x_3206_;
goto v___jp_3177_;
}
else
{
lean_dec(v_a_3176_);
v___y_3178_ = v_e_3165_;
goto v___jp_3177_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v_a_3176_);
lean_dec_ref(v_e_3165_);
v___x_3207_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_3208_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_3207_);
v___y_3178_ = v___x_3208_;
goto v___jp_3177_;
}
v___jp_3177_:
{
lean_object* v___x_3179_; 
lean_inc_ref(v___y_3178_);
v___x_3179_ = l_Lean_Meta_reduceProj_x3f(v___y_3178_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3191_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3191_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3191_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
if (lean_obj_tag(v_a_3180_) == 0)
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___y_3178_);
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___y_3178_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
else
{
lean_object* v_val_3187_; lean_object* v___x_3189_; 
lean_dec_ref(v___y_3178_);
v_val_3187_ = lean_ctor_get(v_a_3180_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v_a_3180_, 1);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v_val_3187_);
v___x_3189_ = v___x_3182_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_val_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v___y_3178_);
v_a_3192_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3179_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3179_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3165_);
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_3209_, uint8_t v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
switch(lean_obj_tag(v_e_3209_))
{
case 7:
{
lean_object* v___x_3218_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3210_ == 0)
{
lean_object* v___x_3219_; lean_object* v_canon_3220_; lean_object* v_cache_3221_; lean_object* v___x_3222_; 
v___x_3219_ = lean_st_ref_get(v_a_3212_);
v_canon_3220_ = lean_ctor_get(v___x_3219_, 10);
lean_inc_ref(v_canon_3220_);
lean_dec(v___x_3219_);
v_cache_3221_ = lean_ctor_get(v_canon_3220_, 0);
lean_inc_ref(v_cache_3221_);
lean_dec_ref(v_canon_3220_);
v___x_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3221_, v_e_3209_);
lean_dec_ref(v_cache_3221_);
if (lean_obj_tag(v___x_3222_) == 1)
{
lean_object* v_val_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_val_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 0);
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_val_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
else
{
lean_object* v___x_3231_; 
lean_dec(v___x_3222_);
lean_inc_ref(v_e_3209_);
v___x_3231_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3218_, v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3271_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3271_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3271_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v_canon_3237_; lean_object* v_share_3238_; lean_object* v_maxFVar_3239_; lean_object* v_proofInstInfo_3240_; lean_object* v_proofInstInfoFVar_3241_; lean_object* v_inferType_3242_; lean_object* v_getLevel_3243_; lean_object* v_congrInfo_3244_; lean_object* v_defEqI_3245_; lean_object* v_extensions_3246_; lean_object* v_issues_3247_; lean_object* v_instanceOverrides_3248_; uint8_t v_debug_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3270_; 
v___x_3236_ = lean_st_ref_take(v_a_3212_);
v_canon_3237_ = lean_ctor_get(v___x_3236_, 10);
v_share_3238_ = lean_ctor_get(v___x_3236_, 0);
v_maxFVar_3239_ = lean_ctor_get(v___x_3236_, 1);
v_proofInstInfo_3240_ = lean_ctor_get(v___x_3236_, 2);
v_proofInstInfoFVar_3241_ = lean_ctor_get(v___x_3236_, 3);
v_inferType_3242_ = lean_ctor_get(v___x_3236_, 4);
v_getLevel_3243_ = lean_ctor_get(v___x_3236_, 5);
v_congrInfo_3244_ = lean_ctor_get(v___x_3236_, 6);
v_defEqI_3245_ = lean_ctor_get(v___x_3236_, 7);
v_extensions_3246_ = lean_ctor_get(v___x_3236_, 8);
v_issues_3247_ = lean_ctor_get(v___x_3236_, 9);
v_instanceOverrides_3248_ = lean_ctor_get(v___x_3236_, 11);
v_debug_3249_ = lean_ctor_get_uint8(v___x_3236_, sizeof(void*)*12);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3251_ = v___x_3236_;
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_instanceOverrides_3248_);
lean_inc(v_canon_3237_);
lean_inc(v_issues_3247_);
lean_inc(v_extensions_3246_);
lean_inc(v_defEqI_3245_);
lean_inc(v_congrInfo_3244_);
lean_inc(v_getLevel_3243_);
lean_inc(v_inferType_3242_);
lean_inc(v_proofInstInfoFVar_3241_);
lean_inc(v_proofInstInfo_3240_);
lean_inc(v_maxFVar_3239_);
lean_inc(v_share_3238_);
lean_dec(v___x_3236_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_cache_3253_; lean_object* v_cacheInType_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3269_; 
v_cache_3253_ = lean_ctor_get(v_canon_3237_, 0);
v_cacheInType_3254_ = lean_ctor_get(v_canon_3237_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_canon_3237_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3256_ = v_canon_3237_;
v_isShared_3257_ = v_isSharedCheck_3269_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_cacheInType_3254_);
lean_inc(v_cache_3253_);
lean_dec(v_canon_3237_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3269_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_inc(v_a_3232_);
v___x_3258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3253_, v_e_3209_, v_a_3232_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3258_);
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_cacheInType_3254_);
v___x_3260_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 10, v___x_3260_);
v___x_3262_ = v___x_3251_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_share_3238_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_maxFVar_3239_);
lean_ctor_set(v_reuseFailAlloc_3267_, 2, v_proofInstInfo_3240_);
lean_ctor_set(v_reuseFailAlloc_3267_, 3, v_proofInstInfoFVar_3241_);
lean_ctor_set(v_reuseFailAlloc_3267_, 4, v_inferType_3242_);
lean_ctor_set(v_reuseFailAlloc_3267_, 5, v_getLevel_3243_);
lean_ctor_set(v_reuseFailAlloc_3267_, 6, v_congrInfo_3244_);
lean_ctor_set(v_reuseFailAlloc_3267_, 7, v_defEqI_3245_);
lean_ctor_set(v_reuseFailAlloc_3267_, 8, v_extensions_3246_);
lean_ctor_set(v_reuseFailAlloc_3267_, 9, v_issues_3247_);
lean_ctor_set(v_reuseFailAlloc_3267_, 10, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3267_, 11, v_instanceOverrides_3248_);
lean_ctor_set_uint8(v_reuseFailAlloc_3267_, sizeof(void*)*12, v_debug_3249_);
v___x_3262_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3263_ = lean_st_ref_put(v_a_3212_, v___x_3262_);
if (v_isShared_3235_ == 0)
{
v___x_3265_ = v___x_3234_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3232_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3231_;
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v_canon_3273_; lean_object* v_cacheInType_3274_; lean_object* v___x_3275_; 
v___x_3272_ = lean_st_ref_get(v_a_3212_);
v_canon_3273_ = lean_ctor_get(v___x_3272_, 10);
lean_inc_ref(v_canon_3273_);
lean_dec(v___x_3272_);
v_cacheInType_3274_ = lean_ctor_get(v_canon_3273_, 1);
lean_inc_ref(v_cacheInType_3274_);
lean_dec_ref(v_canon_3273_);
v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3274_, v_e_3209_);
lean_dec_ref(v_cacheInType_3274_);
if (lean_obj_tag(v___x_3275_) == 1)
{
lean_object* v_val_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_val_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set_tag(v___x_3278_, 0);
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_val_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_object* v___x_3284_; 
lean_dec(v___x_3275_);
lean_inc_ref(v_e_3209_);
v___x_3284_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3218_, v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3324_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3324_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3324_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v_canon_3290_; lean_object* v_share_3291_; lean_object* v_maxFVar_3292_; lean_object* v_proofInstInfo_3293_; lean_object* v_proofInstInfoFVar_3294_; lean_object* v_inferType_3295_; lean_object* v_getLevel_3296_; lean_object* v_congrInfo_3297_; lean_object* v_defEqI_3298_; lean_object* v_extensions_3299_; lean_object* v_issues_3300_; lean_object* v_instanceOverrides_3301_; uint8_t v_debug_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3323_; 
v___x_3289_ = lean_st_ref_take(v_a_3212_);
v_canon_3290_ = lean_ctor_get(v___x_3289_, 10);
v_share_3291_ = lean_ctor_get(v___x_3289_, 0);
v_maxFVar_3292_ = lean_ctor_get(v___x_3289_, 1);
v_proofInstInfo_3293_ = lean_ctor_get(v___x_3289_, 2);
v_proofInstInfoFVar_3294_ = lean_ctor_get(v___x_3289_, 3);
v_inferType_3295_ = lean_ctor_get(v___x_3289_, 4);
v_getLevel_3296_ = lean_ctor_get(v___x_3289_, 5);
v_congrInfo_3297_ = lean_ctor_get(v___x_3289_, 6);
v_defEqI_3298_ = lean_ctor_get(v___x_3289_, 7);
v_extensions_3299_ = lean_ctor_get(v___x_3289_, 8);
v_issues_3300_ = lean_ctor_get(v___x_3289_, 9);
v_instanceOverrides_3301_ = lean_ctor_get(v___x_3289_, 11);
v_debug_3302_ = lean_ctor_get_uint8(v___x_3289_, sizeof(void*)*12);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3304_ = v___x_3289_;
v_isShared_3305_ = v_isSharedCheck_3323_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_instanceOverrides_3301_);
lean_inc(v_canon_3290_);
lean_inc(v_issues_3300_);
lean_inc(v_extensions_3299_);
lean_inc(v_defEqI_3298_);
lean_inc(v_congrInfo_3297_);
lean_inc(v_getLevel_3296_);
lean_inc(v_inferType_3295_);
lean_inc(v_proofInstInfoFVar_3294_);
lean_inc(v_proofInstInfo_3293_);
lean_inc(v_maxFVar_3292_);
lean_inc(v_share_3291_);
lean_dec(v___x_3289_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3323_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_cache_3306_; lean_object* v_cacheInType_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3322_; 
v_cache_3306_ = lean_ctor_get(v_canon_3290_, 0);
v_cacheInType_3307_ = lean_ctor_get(v_canon_3290_, 1);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_canon_3290_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3309_ = v_canon_3290_;
v_isShared_3310_ = v_isSharedCheck_3322_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_cacheInType_3307_);
lean_inc(v_cache_3306_);
lean_dec(v_canon_3290_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3322_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_inc(v_a_3285_);
v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3307_, v_e_3209_, v_a_3285_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_cache_3306_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 10, v___x_3313_);
v___x_3315_ = v___x_3304_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_share_3291_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_maxFVar_3292_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_proofInstInfo_3293_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_proofInstInfoFVar_3294_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_inferType_3295_);
lean_ctor_set(v_reuseFailAlloc_3320_, 5, v_getLevel_3296_);
lean_ctor_set(v_reuseFailAlloc_3320_, 6, v_congrInfo_3297_);
lean_ctor_set(v_reuseFailAlloc_3320_, 7, v_defEqI_3298_);
lean_ctor_set(v_reuseFailAlloc_3320_, 8, v_extensions_3299_);
lean_ctor_set(v_reuseFailAlloc_3320_, 9, v_issues_3300_);
lean_ctor_set(v_reuseFailAlloc_3320_, 10, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3320_, 11, v_instanceOverrides_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3320_, sizeof(void*)*12, v_debug_3302_);
v___x_3315_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = lean_st_ref_put(v_a_3212_, v___x_3315_);
if (v_isShared_3288_ == 0)
{
v___x_3318_ = v___x_3287_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3285_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3284_;
}
}
}
}
case 6:
{
if (v_a_3210_ == 0)
{
lean_object* v___x_3325_; lean_object* v_canon_3326_; lean_object* v_cache_3327_; lean_object* v___x_3328_; 
v___x_3325_ = lean_st_ref_get(v_a_3212_);
v_canon_3326_ = lean_ctor_get(v___x_3325_, 10);
lean_inc_ref(v_canon_3326_);
lean_dec(v___x_3325_);
v_cache_3327_ = lean_ctor_get(v_canon_3326_, 0);
lean_inc_ref(v_cache_3327_);
lean_dec_ref(v_canon_3326_);
v___x_3328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3327_, v_e_3209_);
lean_dec_ref(v_cache_3327_);
if (lean_obj_tag(v___x_3328_) == 1)
{
lean_object* v_val_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_val_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_object* v___x_3337_; 
lean_dec(v___x_3328_);
lean_inc_ref(v_e_3209_);
v___x_3337_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3377_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3377_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3377_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_canon_3343_; lean_object* v_share_3344_; lean_object* v_maxFVar_3345_; lean_object* v_proofInstInfo_3346_; lean_object* v_proofInstInfoFVar_3347_; lean_object* v_inferType_3348_; lean_object* v_getLevel_3349_; lean_object* v_congrInfo_3350_; lean_object* v_defEqI_3351_; lean_object* v_extensions_3352_; lean_object* v_issues_3353_; lean_object* v_instanceOverrides_3354_; uint8_t v_debug_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3376_; 
v___x_3342_ = lean_st_ref_take(v_a_3212_);
v_canon_3343_ = lean_ctor_get(v___x_3342_, 10);
v_share_3344_ = lean_ctor_get(v___x_3342_, 0);
v_maxFVar_3345_ = lean_ctor_get(v___x_3342_, 1);
v_proofInstInfo_3346_ = lean_ctor_get(v___x_3342_, 2);
v_proofInstInfoFVar_3347_ = lean_ctor_get(v___x_3342_, 3);
v_inferType_3348_ = lean_ctor_get(v___x_3342_, 4);
v_getLevel_3349_ = lean_ctor_get(v___x_3342_, 5);
v_congrInfo_3350_ = lean_ctor_get(v___x_3342_, 6);
v_defEqI_3351_ = lean_ctor_get(v___x_3342_, 7);
v_extensions_3352_ = lean_ctor_get(v___x_3342_, 8);
v_issues_3353_ = lean_ctor_get(v___x_3342_, 9);
v_instanceOverrides_3354_ = lean_ctor_get(v___x_3342_, 11);
v_debug_3355_ = lean_ctor_get_uint8(v___x_3342_, sizeof(void*)*12);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3357_ = v___x_3342_;
v_isShared_3358_ = v_isSharedCheck_3376_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_instanceOverrides_3354_);
lean_inc(v_canon_3343_);
lean_inc(v_issues_3353_);
lean_inc(v_extensions_3352_);
lean_inc(v_defEqI_3351_);
lean_inc(v_congrInfo_3350_);
lean_inc(v_getLevel_3349_);
lean_inc(v_inferType_3348_);
lean_inc(v_proofInstInfoFVar_3347_);
lean_inc(v_proofInstInfo_3346_);
lean_inc(v_maxFVar_3345_);
lean_inc(v_share_3344_);
lean_dec(v___x_3342_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3376_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_cache_3359_; lean_object* v_cacheInType_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3375_; 
v_cache_3359_ = lean_ctor_get(v_canon_3343_, 0);
v_cacheInType_3360_ = lean_ctor_get(v_canon_3343_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_canon_3343_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3362_ = v_canon_3343_;
v_isShared_3363_ = v_isSharedCheck_3375_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_cacheInType_3360_);
lean_inc(v_cache_3359_);
lean_dec(v_canon_3343_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3375_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_inc(v_a_3338_);
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3359_, v_e_3209_, v_a_3338_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3364_);
v___x_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_cacheInType_3360_);
v___x_3366_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 10, v___x_3366_);
v___x_3368_ = v___x_3357_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_share_3344_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_maxFVar_3345_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_proofInstInfo_3346_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_proofInstInfoFVar_3347_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v_inferType_3348_);
lean_ctor_set(v_reuseFailAlloc_3373_, 5, v_getLevel_3349_);
lean_ctor_set(v_reuseFailAlloc_3373_, 6, v_congrInfo_3350_);
lean_ctor_set(v_reuseFailAlloc_3373_, 7, v_defEqI_3351_);
lean_ctor_set(v_reuseFailAlloc_3373_, 8, v_extensions_3352_);
lean_ctor_set(v_reuseFailAlloc_3373_, 9, v_issues_3353_);
lean_ctor_set(v_reuseFailAlloc_3373_, 10, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3373_, 11, v_instanceOverrides_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3373_, sizeof(void*)*12, v_debug_3355_);
v___x_3368_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_st_ref_put(v_a_3212_, v___x_3368_);
if (v_isShared_3341_ == 0)
{
v___x_3371_ = v___x_3340_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3338_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3337_;
}
}
}
else
{
lean_object* v___x_3378_; lean_object* v_canon_3379_; lean_object* v_cacheInType_3380_; lean_object* v___x_3381_; 
v___x_3378_ = lean_st_ref_get(v_a_3212_);
v_canon_3379_ = lean_ctor_get(v___x_3378_, 10);
lean_inc_ref(v_canon_3379_);
lean_dec(v___x_3378_);
v_cacheInType_3380_ = lean_ctor_get(v_canon_3379_, 1);
lean_inc_ref(v_cacheInType_3380_);
lean_dec_ref(v_canon_3379_);
v___x_3381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3380_, v_e_3209_);
lean_dec_ref(v_cacheInType_3380_);
if (lean_obj_tag(v___x_3381_) == 1)
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 0);
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_val_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
else
{
lean_object* v___x_3390_; 
lean_dec(v___x_3381_);
lean_inc_ref(v_e_3209_);
v___x_3390_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3430_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3430_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3430_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v_canon_3396_; lean_object* v_share_3397_; lean_object* v_maxFVar_3398_; lean_object* v_proofInstInfo_3399_; lean_object* v_proofInstInfoFVar_3400_; lean_object* v_inferType_3401_; lean_object* v_getLevel_3402_; lean_object* v_congrInfo_3403_; lean_object* v_defEqI_3404_; lean_object* v_extensions_3405_; lean_object* v_issues_3406_; lean_object* v_instanceOverrides_3407_; uint8_t v_debug_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3429_; 
v___x_3395_ = lean_st_ref_take(v_a_3212_);
v_canon_3396_ = lean_ctor_get(v___x_3395_, 10);
v_share_3397_ = lean_ctor_get(v___x_3395_, 0);
v_maxFVar_3398_ = lean_ctor_get(v___x_3395_, 1);
v_proofInstInfo_3399_ = lean_ctor_get(v___x_3395_, 2);
v_proofInstInfoFVar_3400_ = lean_ctor_get(v___x_3395_, 3);
v_inferType_3401_ = lean_ctor_get(v___x_3395_, 4);
v_getLevel_3402_ = lean_ctor_get(v___x_3395_, 5);
v_congrInfo_3403_ = lean_ctor_get(v___x_3395_, 6);
v_defEqI_3404_ = lean_ctor_get(v___x_3395_, 7);
v_extensions_3405_ = lean_ctor_get(v___x_3395_, 8);
v_issues_3406_ = lean_ctor_get(v___x_3395_, 9);
v_instanceOverrides_3407_ = lean_ctor_get(v___x_3395_, 11);
v_debug_3408_ = lean_ctor_get_uint8(v___x_3395_, sizeof(void*)*12);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3410_ = v___x_3395_;
v_isShared_3411_ = v_isSharedCheck_3429_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_instanceOverrides_3407_);
lean_inc(v_canon_3396_);
lean_inc(v_issues_3406_);
lean_inc(v_extensions_3405_);
lean_inc(v_defEqI_3404_);
lean_inc(v_congrInfo_3403_);
lean_inc(v_getLevel_3402_);
lean_inc(v_inferType_3401_);
lean_inc(v_proofInstInfoFVar_3400_);
lean_inc(v_proofInstInfo_3399_);
lean_inc(v_maxFVar_3398_);
lean_inc(v_share_3397_);
lean_dec(v___x_3395_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3429_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_cache_3412_; lean_object* v_cacheInType_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3428_; 
v_cache_3412_ = lean_ctor_get(v_canon_3396_, 0);
v_cacheInType_3413_ = lean_ctor_get(v_canon_3396_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_canon_3396_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3415_ = v_canon_3396_;
v_isShared_3416_ = v_isSharedCheck_3428_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_cacheInType_3413_);
lean_inc(v_cache_3412_);
lean_dec(v_canon_3396_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3428_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_inc(v_a_3391_);
v___x_3417_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3413_, v_e_3209_, v_a_3391_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3417_);
v___x_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_cache_3412_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 10, v___x_3419_);
v___x_3421_ = v___x_3410_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_share_3397_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_maxFVar_3398_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_proofInstInfo_3399_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_proofInstInfoFVar_3400_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v_inferType_3401_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_getLevel_3402_);
lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_congrInfo_3403_);
lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_defEqI_3404_);
lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_extensions_3405_);
lean_ctor_set(v_reuseFailAlloc_3426_, 9, v_issues_3406_);
lean_ctor_set(v_reuseFailAlloc_3426_, 10, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3426_, 11, v_instanceOverrides_3407_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*12, v_debug_3408_);
v___x_3421_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3422_ = lean_st_ref_put(v_a_3212_, v___x_3421_);
if (v_isShared_3394_ == 0)
{
v___x_3424_ = v___x_3393_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3391_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3390_;
}
}
}
}
case 8:
{
lean_object* v___x_3431_; 
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_3210_ == 0)
{
lean_object* v___x_3432_; lean_object* v_canon_3433_; lean_object* v_cache_3434_; lean_object* v___x_3435_; 
v___x_3432_ = lean_st_ref_get(v_a_3212_);
v_canon_3433_ = lean_ctor_get(v___x_3432_, 10);
lean_inc_ref(v_canon_3433_);
lean_dec(v___x_3432_);
v_cache_3434_ = lean_ctor_get(v_canon_3433_, 0);
lean_inc_ref(v_cache_3434_);
lean_dec_ref(v_canon_3433_);
v___x_3435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3434_, v_e_3209_);
lean_dec_ref(v_cache_3434_);
if (lean_obj_tag(v___x_3435_) == 1)
{
lean_object* v_val_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref_known(v_e_3209_, 4);
v_val_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_val_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 0);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_val_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
lean_object* v___x_3444_; 
lean_dec(v___x_3435_);
lean_inc_ref(v_e_3209_);
v___x_3444_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3431_, v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3484_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3484_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3484_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_canon_3450_; lean_object* v_share_3451_; lean_object* v_maxFVar_3452_; lean_object* v_proofInstInfo_3453_; lean_object* v_proofInstInfoFVar_3454_; lean_object* v_inferType_3455_; lean_object* v_getLevel_3456_; lean_object* v_congrInfo_3457_; lean_object* v_defEqI_3458_; lean_object* v_extensions_3459_; lean_object* v_issues_3460_; lean_object* v_instanceOverrides_3461_; uint8_t v_debug_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3483_; 
v___x_3449_ = lean_st_ref_take(v_a_3212_);
v_canon_3450_ = lean_ctor_get(v___x_3449_, 10);
v_share_3451_ = lean_ctor_get(v___x_3449_, 0);
v_maxFVar_3452_ = lean_ctor_get(v___x_3449_, 1);
v_proofInstInfo_3453_ = lean_ctor_get(v___x_3449_, 2);
v_proofInstInfoFVar_3454_ = lean_ctor_get(v___x_3449_, 3);
v_inferType_3455_ = lean_ctor_get(v___x_3449_, 4);
v_getLevel_3456_ = lean_ctor_get(v___x_3449_, 5);
v_congrInfo_3457_ = lean_ctor_get(v___x_3449_, 6);
v_defEqI_3458_ = lean_ctor_get(v___x_3449_, 7);
v_extensions_3459_ = lean_ctor_get(v___x_3449_, 8);
v_issues_3460_ = lean_ctor_get(v___x_3449_, 9);
v_instanceOverrides_3461_ = lean_ctor_get(v___x_3449_, 11);
v_debug_3462_ = lean_ctor_get_uint8(v___x_3449_, sizeof(void*)*12);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3464_ = v___x_3449_;
v_isShared_3465_ = v_isSharedCheck_3483_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_instanceOverrides_3461_);
lean_inc(v_canon_3450_);
lean_inc(v_issues_3460_);
lean_inc(v_extensions_3459_);
lean_inc(v_defEqI_3458_);
lean_inc(v_congrInfo_3457_);
lean_inc(v_getLevel_3456_);
lean_inc(v_inferType_3455_);
lean_inc(v_proofInstInfoFVar_3454_);
lean_inc(v_proofInstInfo_3453_);
lean_inc(v_maxFVar_3452_);
lean_inc(v_share_3451_);
lean_dec(v___x_3449_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3483_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_cache_3466_; lean_object* v_cacheInType_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3482_; 
v_cache_3466_ = lean_ctor_get(v_canon_3450_, 0);
v_cacheInType_3467_ = lean_ctor_get(v_canon_3450_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_canon_3450_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3469_ = v_canon_3450_;
v_isShared_3470_ = v_isSharedCheck_3482_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_cacheInType_3467_);
lean_inc(v_cache_3466_);
lean_dec(v_canon_3450_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3482_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
lean_inc(v_a_3445_);
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3466_, v_e_3209_, v_a_3445_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_cacheInType_3467_);
v___x_3473_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 10, v___x_3473_);
v___x_3475_ = v___x_3464_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_share_3451_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_maxFVar_3452_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_proofInstInfo_3453_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_proofInstInfoFVar_3454_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_inferType_3455_);
lean_ctor_set(v_reuseFailAlloc_3480_, 5, v_getLevel_3456_);
lean_ctor_set(v_reuseFailAlloc_3480_, 6, v_congrInfo_3457_);
lean_ctor_set(v_reuseFailAlloc_3480_, 7, v_defEqI_3458_);
lean_ctor_set(v_reuseFailAlloc_3480_, 8, v_extensions_3459_);
lean_ctor_set(v_reuseFailAlloc_3480_, 9, v_issues_3460_);
lean_ctor_set(v_reuseFailAlloc_3480_, 10, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3480_, 11, v_instanceOverrides_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, sizeof(void*)*12, v_debug_3462_);
v___x_3475_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_st_ref_put(v_a_3212_, v___x_3475_);
if (v_isShared_3448_ == 0)
{
v___x_3478_ = v___x_3447_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3445_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 4);
return v___x_3444_;
}
}
}
else
{
lean_object* v___x_3485_; lean_object* v_canon_3486_; lean_object* v_cacheInType_3487_; lean_object* v___x_3488_; 
v___x_3485_ = lean_st_ref_get(v_a_3212_);
v_canon_3486_ = lean_ctor_get(v___x_3485_, 10);
lean_inc_ref(v_canon_3486_);
lean_dec(v___x_3485_);
v_cacheInType_3487_ = lean_ctor_get(v_canon_3486_, 1);
lean_inc_ref(v_cacheInType_3487_);
lean_dec_ref(v_canon_3486_);
v___x_3488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3487_, v_e_3209_);
lean_dec_ref(v_cacheInType_3487_);
if (lean_obj_tag(v___x_3488_) == 1)
{
lean_object* v_val_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref_known(v_e_3209_, 4);
v_val_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_val_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 0);
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_val_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_object* v___x_3497_; 
lean_dec(v___x_3488_);
lean_inc_ref(v_e_3209_);
v___x_3497_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_3431_, v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3537_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3537_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3537_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v_canon_3503_; lean_object* v_share_3504_; lean_object* v_maxFVar_3505_; lean_object* v_proofInstInfo_3506_; lean_object* v_proofInstInfoFVar_3507_; lean_object* v_inferType_3508_; lean_object* v_getLevel_3509_; lean_object* v_congrInfo_3510_; lean_object* v_defEqI_3511_; lean_object* v_extensions_3512_; lean_object* v_issues_3513_; lean_object* v_instanceOverrides_3514_; uint8_t v_debug_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3536_; 
v___x_3502_ = lean_st_ref_take(v_a_3212_);
v_canon_3503_ = lean_ctor_get(v___x_3502_, 10);
v_share_3504_ = lean_ctor_get(v___x_3502_, 0);
v_maxFVar_3505_ = lean_ctor_get(v___x_3502_, 1);
v_proofInstInfo_3506_ = lean_ctor_get(v___x_3502_, 2);
v_proofInstInfoFVar_3507_ = lean_ctor_get(v___x_3502_, 3);
v_inferType_3508_ = lean_ctor_get(v___x_3502_, 4);
v_getLevel_3509_ = lean_ctor_get(v___x_3502_, 5);
v_congrInfo_3510_ = lean_ctor_get(v___x_3502_, 6);
v_defEqI_3511_ = lean_ctor_get(v___x_3502_, 7);
v_extensions_3512_ = lean_ctor_get(v___x_3502_, 8);
v_issues_3513_ = lean_ctor_get(v___x_3502_, 9);
v_instanceOverrides_3514_ = lean_ctor_get(v___x_3502_, 11);
v_debug_3515_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*12);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3517_ = v___x_3502_;
v_isShared_3518_ = v_isSharedCheck_3536_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_instanceOverrides_3514_);
lean_inc(v_canon_3503_);
lean_inc(v_issues_3513_);
lean_inc(v_extensions_3512_);
lean_inc(v_defEqI_3511_);
lean_inc(v_congrInfo_3510_);
lean_inc(v_getLevel_3509_);
lean_inc(v_inferType_3508_);
lean_inc(v_proofInstInfoFVar_3507_);
lean_inc(v_proofInstInfo_3506_);
lean_inc(v_maxFVar_3505_);
lean_inc(v_share_3504_);
lean_dec(v___x_3502_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3536_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_cache_3519_; lean_object* v_cacheInType_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3535_; 
v_cache_3519_ = lean_ctor_get(v_canon_3503_, 0);
v_cacheInType_3520_ = lean_ctor_get(v_canon_3503_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_canon_3503_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3522_ = v_canon_3503_;
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_cacheInType_3520_);
lean_inc(v_cache_3519_);
lean_dec(v_canon_3503_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_inc(v_a_3498_);
v___x_3524_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3520_, v_e_3209_, v_a_3498_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 1, v___x_3524_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_cache_3519_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 10, v___x_3526_);
v___x_3528_ = v___x_3517_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_share_3504_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_maxFVar_3505_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_proofInstInfo_3506_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_proofInstInfoFVar_3507_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_inferType_3508_);
lean_ctor_set(v_reuseFailAlloc_3533_, 5, v_getLevel_3509_);
lean_ctor_set(v_reuseFailAlloc_3533_, 6, v_congrInfo_3510_);
lean_ctor_set(v_reuseFailAlloc_3533_, 7, v_defEqI_3511_);
lean_ctor_set(v_reuseFailAlloc_3533_, 8, v_extensions_3512_);
lean_ctor_set(v_reuseFailAlloc_3533_, 9, v_issues_3513_);
lean_ctor_set(v_reuseFailAlloc_3533_, 10, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3533_, 11, v_instanceOverrides_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*12, v_debug_3515_);
v___x_3528_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_st_ref_put(v_a_3212_, v___x_3528_);
if (v_isShared_3501_ == 0)
{
v___x_3531_ = v___x_3500_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3498_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 4);
return v___x_3497_;
}
}
}
}
case 5:
{
if (v_a_3210_ == 0)
{
lean_object* v___x_3538_; lean_object* v_canon_3539_; lean_object* v_cache_3540_; lean_object* v___x_3541_; 
v___x_3538_ = lean_st_ref_get(v_a_3212_);
v_canon_3539_ = lean_ctor_get(v___x_3538_, 10);
lean_inc_ref(v_canon_3539_);
lean_dec(v___x_3538_);
v_cache_3540_ = lean_ctor_get(v_canon_3539_, 0);
lean_inc_ref(v_cache_3540_);
lean_dec_ref(v_canon_3539_);
v___x_3541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3540_, v_e_3209_);
lean_dec_ref(v_cache_3540_);
if (lean_obj_tag(v___x_3541_) == 1)
{
lean_object* v_val_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref_known(v_e_3209_, 2);
v_val_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_val_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 0);
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_val_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
else
{
lean_object* v___x_3550_; 
lean_dec(v___x_3541_);
lean_inc_ref(v_e_3209_);
v___x_3550_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3590_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3590_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3590_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v_canon_3556_; lean_object* v_share_3557_; lean_object* v_maxFVar_3558_; lean_object* v_proofInstInfo_3559_; lean_object* v_proofInstInfoFVar_3560_; lean_object* v_inferType_3561_; lean_object* v_getLevel_3562_; lean_object* v_congrInfo_3563_; lean_object* v_defEqI_3564_; lean_object* v_extensions_3565_; lean_object* v_issues_3566_; lean_object* v_instanceOverrides_3567_; uint8_t v_debug_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3589_; 
v___x_3555_ = lean_st_ref_take(v_a_3212_);
v_canon_3556_ = lean_ctor_get(v___x_3555_, 10);
v_share_3557_ = lean_ctor_get(v___x_3555_, 0);
v_maxFVar_3558_ = lean_ctor_get(v___x_3555_, 1);
v_proofInstInfo_3559_ = lean_ctor_get(v___x_3555_, 2);
v_proofInstInfoFVar_3560_ = lean_ctor_get(v___x_3555_, 3);
v_inferType_3561_ = lean_ctor_get(v___x_3555_, 4);
v_getLevel_3562_ = lean_ctor_get(v___x_3555_, 5);
v_congrInfo_3563_ = lean_ctor_get(v___x_3555_, 6);
v_defEqI_3564_ = lean_ctor_get(v___x_3555_, 7);
v_extensions_3565_ = lean_ctor_get(v___x_3555_, 8);
v_issues_3566_ = lean_ctor_get(v___x_3555_, 9);
v_instanceOverrides_3567_ = lean_ctor_get(v___x_3555_, 11);
v_debug_3568_ = lean_ctor_get_uint8(v___x_3555_, sizeof(void*)*12);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3570_ = v___x_3555_;
v_isShared_3571_ = v_isSharedCheck_3589_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_instanceOverrides_3567_);
lean_inc(v_canon_3556_);
lean_inc(v_issues_3566_);
lean_inc(v_extensions_3565_);
lean_inc(v_defEqI_3564_);
lean_inc(v_congrInfo_3563_);
lean_inc(v_getLevel_3562_);
lean_inc(v_inferType_3561_);
lean_inc(v_proofInstInfoFVar_3560_);
lean_inc(v_proofInstInfo_3559_);
lean_inc(v_maxFVar_3558_);
lean_inc(v_share_3557_);
lean_dec(v___x_3555_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3589_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_cache_3572_; lean_object* v_cacheInType_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3588_; 
v_cache_3572_ = lean_ctor_get(v_canon_3556_, 0);
v_cacheInType_3573_ = lean_ctor_get(v_canon_3556_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_canon_3556_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3575_ = v_canon_3556_;
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_cacheInType_3573_);
lean_inc(v_cache_3572_);
lean_dec(v_canon_3556_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_inc(v_a_3551_);
v___x_3577_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3572_, v_e_3209_, v_a_3551_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3577_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_cacheInType_3573_);
v___x_3579_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 10, v___x_3579_);
v___x_3581_ = v___x_3570_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_share_3557_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_maxFVar_3558_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_proofInstInfo_3559_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v_proofInstInfoFVar_3560_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v_inferType_3561_);
lean_ctor_set(v_reuseFailAlloc_3586_, 5, v_getLevel_3562_);
lean_ctor_set(v_reuseFailAlloc_3586_, 6, v_congrInfo_3563_);
lean_ctor_set(v_reuseFailAlloc_3586_, 7, v_defEqI_3564_);
lean_ctor_set(v_reuseFailAlloc_3586_, 8, v_extensions_3565_);
lean_ctor_set(v_reuseFailAlloc_3586_, 9, v_issues_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 10, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3586_, 11, v_instanceOverrides_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*12, v_debug_3568_);
v___x_3581_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_st_ref_put(v_a_3212_, v___x_3581_);
if (v_isShared_3554_ == 0)
{
v___x_3584_ = v___x_3553_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3551_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 2);
return v___x_3550_;
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v_canon_3592_; lean_object* v_cacheInType_3593_; lean_object* v___x_3594_; 
v___x_3591_ = lean_st_ref_get(v_a_3212_);
v_canon_3592_ = lean_ctor_get(v___x_3591_, 10);
lean_inc_ref(v_canon_3592_);
lean_dec(v___x_3591_);
v_cacheInType_3593_ = lean_ctor_get(v_canon_3592_, 1);
lean_inc_ref(v_cacheInType_3593_);
lean_dec_ref(v_canon_3592_);
v___x_3594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3593_, v_e_3209_);
lean_dec_ref(v_cacheInType_3593_);
if (lean_obj_tag(v___x_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref_known(v_e_3209_, 2);
v_val_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_val_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 0);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_val_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
lean_object* v___x_3603_; 
lean_dec(v___x_3594_);
lean_inc_ref(v_e_3209_);
v___x_3603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3643_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3643_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3643_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v_canon_3609_; lean_object* v_share_3610_; lean_object* v_maxFVar_3611_; lean_object* v_proofInstInfo_3612_; lean_object* v_proofInstInfoFVar_3613_; lean_object* v_inferType_3614_; lean_object* v_getLevel_3615_; lean_object* v_congrInfo_3616_; lean_object* v_defEqI_3617_; lean_object* v_extensions_3618_; lean_object* v_issues_3619_; lean_object* v_instanceOverrides_3620_; uint8_t v_debug_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3642_; 
v___x_3608_ = lean_st_ref_take(v_a_3212_);
v_canon_3609_ = lean_ctor_get(v___x_3608_, 10);
v_share_3610_ = lean_ctor_get(v___x_3608_, 0);
v_maxFVar_3611_ = lean_ctor_get(v___x_3608_, 1);
v_proofInstInfo_3612_ = lean_ctor_get(v___x_3608_, 2);
v_proofInstInfoFVar_3613_ = lean_ctor_get(v___x_3608_, 3);
v_inferType_3614_ = lean_ctor_get(v___x_3608_, 4);
v_getLevel_3615_ = lean_ctor_get(v___x_3608_, 5);
v_congrInfo_3616_ = lean_ctor_get(v___x_3608_, 6);
v_defEqI_3617_ = lean_ctor_get(v___x_3608_, 7);
v_extensions_3618_ = lean_ctor_get(v___x_3608_, 8);
v_issues_3619_ = lean_ctor_get(v___x_3608_, 9);
v_instanceOverrides_3620_ = lean_ctor_get(v___x_3608_, 11);
v_debug_3621_ = lean_ctor_get_uint8(v___x_3608_, sizeof(void*)*12);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3623_ = v___x_3608_;
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_instanceOverrides_3620_);
lean_inc(v_canon_3609_);
lean_inc(v_issues_3619_);
lean_inc(v_extensions_3618_);
lean_inc(v_defEqI_3617_);
lean_inc(v_congrInfo_3616_);
lean_inc(v_getLevel_3615_);
lean_inc(v_inferType_3614_);
lean_inc(v_proofInstInfoFVar_3613_);
lean_inc(v_proofInstInfo_3612_);
lean_inc(v_maxFVar_3611_);
lean_inc(v_share_3610_);
lean_dec(v___x_3608_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v_cache_3625_; lean_object* v_cacheInType_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3641_; 
v_cache_3625_ = lean_ctor_get(v_canon_3609_, 0);
v_cacheInType_3626_ = lean_ctor_get(v_canon_3609_, 1);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_canon_3609_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3628_ = v_canon_3609_;
v_isShared_3629_ = v_isSharedCheck_3641_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_cacheInType_3626_);
lean_inc(v_cache_3625_);
lean_dec(v_canon_3609_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3641_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
lean_inc(v_a_3604_);
v___x_3630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3626_, v_e_3209_, v_a_3604_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v___x_3630_);
v___x_3632_ = v___x_3628_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_cache_3625_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 10, v___x_3632_);
v___x_3634_ = v___x_3623_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_share_3610_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_maxFVar_3611_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_proofInstInfo_3612_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_proofInstInfoFVar_3613_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_inferType_3614_);
lean_ctor_set(v_reuseFailAlloc_3639_, 5, v_getLevel_3615_);
lean_ctor_set(v_reuseFailAlloc_3639_, 6, v_congrInfo_3616_);
lean_ctor_set(v_reuseFailAlloc_3639_, 7, v_defEqI_3617_);
lean_ctor_set(v_reuseFailAlloc_3639_, 8, v_extensions_3618_);
lean_ctor_set(v_reuseFailAlloc_3639_, 9, v_issues_3619_);
lean_ctor_set(v_reuseFailAlloc_3639_, 10, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3639_, 11, v_instanceOverrides_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*12, v_debug_3621_);
v___x_3634_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3635_ = lean_st_ref_put(v_a_3212_, v___x_3634_);
if (v_isShared_3607_ == 0)
{
v___x_3637_ = v___x_3606_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3604_);
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
}
}
else
{
lean_dec_ref_known(v_e_3209_, 2);
return v___x_3603_;
}
}
}
}
case 11:
{
if (v_a_3210_ == 0)
{
lean_object* v___x_3644_; lean_object* v_canon_3645_; lean_object* v_cache_3646_; lean_object* v___x_3647_; 
v___x_3644_ = lean_st_ref_get(v_a_3212_);
v_canon_3645_ = lean_ctor_get(v___x_3644_, 10);
lean_inc_ref(v_canon_3645_);
lean_dec(v___x_3644_);
v_cache_3646_ = lean_ctor_get(v_canon_3645_, 0);
lean_inc_ref(v_cache_3646_);
lean_dec_ref(v_canon_3645_);
v___x_3647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3646_, v_e_3209_);
lean_dec_ref(v_cache_3646_);
if (lean_obj_tag(v___x_3647_) == 1)
{
lean_object* v_val_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_val_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 0);
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_val_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
else
{
lean_object* v___x_3656_; 
lean_dec(v___x_3647_);
lean_inc_ref(v_e_3209_);
v___x_3656_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3696_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3696_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3696_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v_canon_3662_; lean_object* v_share_3663_; lean_object* v_maxFVar_3664_; lean_object* v_proofInstInfo_3665_; lean_object* v_proofInstInfoFVar_3666_; lean_object* v_inferType_3667_; lean_object* v_getLevel_3668_; lean_object* v_congrInfo_3669_; lean_object* v_defEqI_3670_; lean_object* v_extensions_3671_; lean_object* v_issues_3672_; lean_object* v_instanceOverrides_3673_; uint8_t v_debug_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3695_; 
v___x_3661_ = lean_st_ref_take(v_a_3212_);
v_canon_3662_ = lean_ctor_get(v___x_3661_, 10);
v_share_3663_ = lean_ctor_get(v___x_3661_, 0);
v_maxFVar_3664_ = lean_ctor_get(v___x_3661_, 1);
v_proofInstInfo_3665_ = lean_ctor_get(v___x_3661_, 2);
v_proofInstInfoFVar_3666_ = lean_ctor_get(v___x_3661_, 3);
v_inferType_3667_ = lean_ctor_get(v___x_3661_, 4);
v_getLevel_3668_ = lean_ctor_get(v___x_3661_, 5);
v_congrInfo_3669_ = lean_ctor_get(v___x_3661_, 6);
v_defEqI_3670_ = lean_ctor_get(v___x_3661_, 7);
v_extensions_3671_ = lean_ctor_get(v___x_3661_, 8);
v_issues_3672_ = lean_ctor_get(v___x_3661_, 9);
v_instanceOverrides_3673_ = lean_ctor_get(v___x_3661_, 11);
v_debug_3674_ = lean_ctor_get_uint8(v___x_3661_, sizeof(void*)*12);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3676_ = v___x_3661_;
v_isShared_3677_ = v_isSharedCheck_3695_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_instanceOverrides_3673_);
lean_inc(v_canon_3662_);
lean_inc(v_issues_3672_);
lean_inc(v_extensions_3671_);
lean_inc(v_defEqI_3670_);
lean_inc(v_congrInfo_3669_);
lean_inc(v_getLevel_3668_);
lean_inc(v_inferType_3667_);
lean_inc(v_proofInstInfoFVar_3666_);
lean_inc(v_proofInstInfo_3665_);
lean_inc(v_maxFVar_3664_);
lean_inc(v_share_3663_);
lean_dec(v___x_3661_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3695_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_cache_3678_; lean_object* v_cacheInType_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3694_; 
v_cache_3678_ = lean_ctor_get(v_canon_3662_, 0);
v_cacheInType_3679_ = lean_ctor_get(v_canon_3662_, 1);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_canon_3662_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3681_ = v_canon_3662_;
v_isShared_3682_ = v_isSharedCheck_3694_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_cacheInType_3679_);
lean_inc(v_cache_3678_);
lean_dec(v_canon_3662_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3694_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
lean_inc(v_a_3657_);
v___x_3683_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3678_, v_e_3209_, v_a_3657_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3683_);
v___x_3685_ = v___x_3681_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_cacheInType_3679_);
v___x_3685_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 10, v___x_3685_);
v___x_3687_ = v___x_3676_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_share_3663_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_maxFVar_3664_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_proofInstInfo_3665_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_proofInstInfoFVar_3666_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_inferType_3667_);
lean_ctor_set(v_reuseFailAlloc_3692_, 5, v_getLevel_3668_);
lean_ctor_set(v_reuseFailAlloc_3692_, 6, v_congrInfo_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 7, v_defEqI_3670_);
lean_ctor_set(v_reuseFailAlloc_3692_, 8, v_extensions_3671_);
lean_ctor_set(v_reuseFailAlloc_3692_, 9, v_issues_3672_);
lean_ctor_set(v_reuseFailAlloc_3692_, 10, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3692_, 11, v_instanceOverrides_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*12, v_debug_3674_);
v___x_3687_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_st_ref_put(v_a_3212_, v___x_3687_);
if (v_isShared_3660_ == 0)
{
v___x_3690_ = v___x_3659_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3657_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3697_; lean_object* v_canon_3698_; lean_object* v_cacheInType_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_st_ref_get(v_a_3212_);
v_canon_3698_ = lean_ctor_get(v___x_3697_, 10);
lean_inc_ref(v_canon_3698_);
lean_dec(v___x_3697_);
v_cacheInType_3699_ = lean_ctor_get(v_canon_3698_, 1);
lean_inc_ref(v_cacheInType_3699_);
lean_dec_ref(v_canon_3698_);
v___x_3700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3699_, v_e_3209_);
lean_dec_ref(v_cacheInType_3699_);
if (lean_obj_tag(v___x_3700_) == 1)
{
lean_object* v_val_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref_known(v_e_3209_, 3);
v_val_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_val_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
lean_ctor_set_tag(v___x_3703_, 0);
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_val_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
lean_object* v___x_3709_; 
lean_dec(v___x_3700_);
lean_inc_ref(v_e_3209_);
v___x_3709_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3749_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3749_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3749_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; lean_object* v_canon_3715_; lean_object* v_share_3716_; lean_object* v_maxFVar_3717_; lean_object* v_proofInstInfo_3718_; lean_object* v_proofInstInfoFVar_3719_; lean_object* v_inferType_3720_; lean_object* v_getLevel_3721_; lean_object* v_congrInfo_3722_; lean_object* v_defEqI_3723_; lean_object* v_extensions_3724_; lean_object* v_issues_3725_; lean_object* v_instanceOverrides_3726_; uint8_t v_debug_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3748_; 
v___x_3714_ = lean_st_ref_take(v_a_3212_);
v_canon_3715_ = lean_ctor_get(v___x_3714_, 10);
v_share_3716_ = lean_ctor_get(v___x_3714_, 0);
v_maxFVar_3717_ = lean_ctor_get(v___x_3714_, 1);
v_proofInstInfo_3718_ = lean_ctor_get(v___x_3714_, 2);
v_proofInstInfoFVar_3719_ = lean_ctor_get(v___x_3714_, 3);
v_inferType_3720_ = lean_ctor_get(v___x_3714_, 4);
v_getLevel_3721_ = lean_ctor_get(v___x_3714_, 5);
v_congrInfo_3722_ = lean_ctor_get(v___x_3714_, 6);
v_defEqI_3723_ = lean_ctor_get(v___x_3714_, 7);
v_extensions_3724_ = lean_ctor_get(v___x_3714_, 8);
v_issues_3725_ = lean_ctor_get(v___x_3714_, 9);
v_instanceOverrides_3726_ = lean_ctor_get(v___x_3714_, 11);
v_debug_3727_ = lean_ctor_get_uint8(v___x_3714_, sizeof(void*)*12);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3729_ = v___x_3714_;
v_isShared_3730_ = v_isSharedCheck_3748_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_instanceOverrides_3726_);
lean_inc(v_canon_3715_);
lean_inc(v_issues_3725_);
lean_inc(v_extensions_3724_);
lean_inc(v_defEqI_3723_);
lean_inc(v_congrInfo_3722_);
lean_inc(v_getLevel_3721_);
lean_inc(v_inferType_3720_);
lean_inc(v_proofInstInfoFVar_3719_);
lean_inc(v_proofInstInfo_3718_);
lean_inc(v_maxFVar_3717_);
lean_inc(v_share_3716_);
lean_dec(v___x_3714_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3748_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_cache_3731_; lean_object* v_cacheInType_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3747_; 
v_cache_3731_ = lean_ctor_get(v_canon_3715_, 0);
v_cacheInType_3732_ = lean_ctor_get(v_canon_3715_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_canon_3715_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3734_ = v_canon_3715_;
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_cacheInType_3732_);
lean_inc(v_cache_3731_);
lean_dec(v_canon_3715_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_inc(v_a_3710_);
v___x_3736_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3732_, v_e_3209_, v_a_3710_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v___x_3736_);
v___x_3738_ = v___x_3734_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_cache_3731_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 10, v___x_3738_);
v___x_3740_ = v___x_3729_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_share_3716_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_maxFVar_3717_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_proofInstInfo_3718_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_proofInstInfoFVar_3719_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_inferType_3720_);
lean_ctor_set(v_reuseFailAlloc_3745_, 5, v_getLevel_3721_);
lean_ctor_set(v_reuseFailAlloc_3745_, 6, v_congrInfo_3722_);
lean_ctor_set(v_reuseFailAlloc_3745_, 7, v_defEqI_3723_);
lean_ctor_set(v_reuseFailAlloc_3745_, 8, v_extensions_3724_);
lean_ctor_set(v_reuseFailAlloc_3745_, 9, v_issues_3725_);
lean_ctor_set(v_reuseFailAlloc_3745_, 10, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3745_, 11, v_instanceOverrides_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*12, v_debug_3727_);
v___x_3740_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = lean_st_ref_put(v_a_3212_, v___x_3740_);
if (v_isShared_3713_ == 0)
{
v___x_3743_ = v___x_3712_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3710_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 3);
return v___x_3709_;
}
}
}
}
case 10:
{
lean_object* v_data_3750_; lean_object* v_expr_3751_; lean_object* v___x_3752_; 
v_data_3750_ = lean_ctor_get(v_e_3209_, 0);
v_expr_3751_ = lean_ctor_get(v_e_3209_, 1);
lean_inc_ref(v_expr_3751_);
v___x_3752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3751_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3767_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3767_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3767_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
size_t v___x_3757_; size_t v___x_3758_; uint8_t v___x_3759_; 
v___x_3757_ = lean_ptr_addr(v_expr_3751_);
v___x_3758_ = lean_ptr_addr(v_a_3753_);
v___x_3759_ = lean_usize_dec_eq(v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_inc(v_data_3750_);
lean_dec_ref_known(v_e_3209_, 2);
v___x_3760_ = l_Lean_Expr_mdata___override(v_data_3750_, v_a_3753_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3760_);
v___x_3762_ = v___x_3755_;
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
else
{
lean_object* v___x_3765_; 
lean_dec(v_a_3753_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v_e_3209_);
v___x_3765_ = v___x_3755_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_e_3209_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3209_, 2);
return v___x_3752_;
}
}
default: 
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_e_3209_);
return v___x_3768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3769_, uint8_t v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
if (v_a_3770_ == 0)
{
uint8_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = 1;
lean_inc_ref(v_e_3769_);
v___x_3779_ = l_Lean_Meta_isProp(v_e_3769_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; uint8_t v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = lean_unbox(v_a_3780_);
lean_dec(v_a_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3769_, v___x_3778_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3782_;
}
else
{
lean_object* v___x_3783_; 
v___x_3783_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3783_;
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v_e_3769_);
v_a_3784_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3779_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3779_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v___x_3792_; 
v___x_3792_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3793_, lean_object* v_e_3794_, uint8_t v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
if (lean_obj_tag(v_e_3794_) == 7)
{
lean_object* v_binderName_3803_; lean_object* v_binderType_3804_; lean_object* v_body_3805_; uint8_t v_binderInfo_3806_; lean_object* v___f_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_binderName_3803_ = lean_ctor_get(v_e_3794_, 0);
lean_inc(v_binderName_3803_);
v_binderType_3804_ = lean_ctor_get(v_e_3794_, 1);
lean_inc_ref(v_binderType_3804_);
v_body_3805_ = lean_ctor_get(v_e_3794_, 2);
lean_inc_ref(v_body_3805_);
v_binderInfo_3806_ = lean_ctor_get_uint8(v_e_3794_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3794_, 3);
lean_inc_ref(v_fvars_3793_);
v___f_3807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3807_, 0, v_fvars_3793_);
lean_closure_set(v___f_3807_, 1, v_body_3805_);
v___x_3808_ = lean_expr_instantiate_rev(v_binderType_3804_, v_fvars_3793_);
lean_dec_ref(v_fvars_3793_);
lean_dec_ref(v_binderType_3804_);
v___x_3809_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3808_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = 0;
v___x_3812_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(v_binderName_3803_, v_binderInfo_3806_, v_a_3810_, v___f_3807_, v___x_3811_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
return v___x_3812_;
}
else
{
lean_dec_ref(v___f_3807_);
lean_dec(v_binderName_3803_);
return v___x_3809_;
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_expr_instantiate_rev(v_e_3794_, v_fvars_3793_);
lean_dec_ref(v_e_3794_);
v___x_3814_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3813_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; uint8_t v___x_3816_; uint8_t v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = 0;
v___x_3817_ = 1;
v___x_3818_ = 1;
v___x_3819_ = l_Lean_Meta_mkForallFVars(v_fvars_3793_, v_a_3815_, v___x_3816_, v___x_3817_, v___x_3817_, v___x_3818_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec_ref(v_fvars_3793_);
return v___x_3819_;
}
else
{
lean_dec_ref(v_fvars_3793_);
return v___x_3814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3820_, lean_object* v_body_3821_, lean_object* v_x_3822_, uint8_t v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_array_push(v_fvars_3820_, v_x_3822_);
v___x_3832_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3831_, v_body_3821_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
uint8_t v_a_boxed_3842_; lean_object* v_res_3843_; 
v_a_boxed_3842_ = lean_unbox(v_a_3834_);
v_res_3843_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3833_, v_a_boxed_3842_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
uint8_t v_a_boxed_3853_; lean_object* v_res_3854_; 
v_a_boxed_3853_ = lean_unbox(v_a_3845_);
v_res_3854_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3844_, v_a_boxed_3853_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
uint8_t v_a_boxed_3864_; lean_object* v_res_3865_; 
v_a_boxed_3864_ = lean_unbox(v_a_3856_);
v_res_3865_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3855_, v_a_boxed_3864_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst___boxed(lean_object* v_ofNat_3866_, lean_object* v_00_u03b1_3867_, lean_object* v_n_3868_, lean_object* v_inst_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
uint8_t v_a_boxed_3878_; lean_object* v_res_3879_; 
v_a_boxed_3878_ = lean_unbox(v_a_3870_);
v_res_3879_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonOfNatInst(v_ofNat_3866_, v_00_u03b1_3867_, v_n_3868_, v_inst_3869_, v_a_boxed_3878_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec_ref(v_ofNat_3866_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
uint8_t v_a_boxed_3889_; lean_object* v_res_3890_; 
v_a_boxed_3889_ = lean_unbox(v_a_3881_);
v_res_3890_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3880_, v_a_boxed_3889_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
lean_dec(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
uint8_t v_a_boxed_3900_; lean_object* v_res_3901_; 
v_a_boxed_3900_ = lean_unbox(v_a_3892_);
v_res_3901_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3891_, v_a_boxed_3900_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3902_, lean_object* v_e_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
uint8_t v_a_boxed_3912_; lean_object* v_res_3913_; 
v_a_boxed_3912_ = lean_unbox(v_a_3904_);
v_res_3913_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3902_, v_e_3903_, v_a_boxed_3912_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3914_, lean_object* v_e_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
uint8_t v_a_boxed_3924_; lean_object* v_res_3925_; 
v_a_boxed_3924_ = lean_unbox(v_a_3916_);
v_res_3925_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3914_, v_e_3915_, v_a_boxed_3924_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3926_, lean_object* v_report_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
uint8_t v_report_boxed_3936_; uint8_t v_a_boxed_3937_; lean_object* v_res_3938_; 
v_report_boxed_3936_ = lean_unbox(v_report_3927_);
v_a_boxed_3937_ = lean_unbox(v_a_3928_);
v_res_3938_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3926_, v_report_boxed_3936_, v_a_boxed_3937_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
uint8_t v_a_boxed_3948_; lean_object* v_res_3949_; 
v_a_boxed_3948_ = lean_unbox(v_a_3940_);
v_res_3949_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3939_, v_a_boxed_3948_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3950_, lean_object* v_e_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
uint8_t v_a_boxed_3960_; lean_object* v_res_3961_; 
v_a_boxed_3960_ = lean_unbox(v_a_3952_);
v_res_3961_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3950_, v_e_3951_, v_a_boxed_3960_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3962_, lean_object* v_00_u03b1_3963_, lean_object* v_c_3964_, lean_object* v_a_3965_, lean_object* v_b_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
uint8_t v_a_boxed_3975_; lean_object* v_res_3976_; 
v_a_boxed_3975_ = lean_unbox(v_a_3967_);
v_res_3976_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3962_, v_00_u03b1_3963_, v_c_3964_, v_a_3965_, v_b_3966_, v_a_boxed_3975_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3977_, lean_object* v_00_u03b1_3978_, lean_object* v_c_3979_, lean_object* v_inst_3980_, lean_object* v_a_3981_, lean_object* v_b_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
uint8_t v_a_boxed_3991_; lean_object* v_res_3992_; 
v_a_boxed_3991_ = lean_unbox(v_a_3983_);
v_res_3992_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3977_, v_00_u03b1_3978_, v_c_3979_, v_inst_3980_, v_a_3981_, v_b_3982_, v_a_boxed_3991_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
uint8_t v_a_boxed_4002_; lean_object* v_res_4003_; 
v_a_boxed_4002_ = lean_unbox(v_a_3994_);
v_res_4003_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3993_, v_a_boxed_4002_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
uint8_t v_a_boxed_4013_; lean_object* v_res_4014_; 
v_a_boxed_4013_ = lean_unbox(v_a_4005_);
v_res_4014_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_4004_, v_a_boxed_4013_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_4015_, lean_object* v_prop_4016_, lean_object* v_inst_4017_, lean_object* v_e_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
uint8_t v_a_boxed_4027_; lean_object* v_res_4028_; 
v_a_boxed_4027_ = lean_unbox(v_a_4019_);
v_res_4028_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_4015_, v_prop_4016_, v_inst_4017_, v_e_4018_, v_a_boxed_4027_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_4029_, lean_object* v_report_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
uint8_t v_report_boxed_4039_; uint8_t v_a_boxed_4040_; lean_object* v_res_4041_; 
v_report_boxed_4039_ = lean_unbox(v_report_4030_);
v_a_boxed_4040_ = lean_unbox(v_a_4031_);
v_res_4041_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_4029_, v_report_boxed_4039_, v_a_boxed_4040_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_4042_, lean_object* v_prop_4043_, lean_object* v_h_4044_, lean_object* v_e_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
uint8_t v_a_boxed_4054_; lean_object* v_res_4055_; 
v_a_boxed_4054_ = lean_unbox(v_a_4046_);
v_res_4055_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_4042_, v_prop_4043_, v_h_4044_, v_e_4045_, v_a_boxed_4054_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_4056_, lean_object* v_type_4057_, lean_object* v_report_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
uint8_t v_report_boxed_4067_; uint8_t v_a_boxed_4068_; lean_object* v_res_4069_; 
v_report_boxed_4067_ = lean_unbox(v_report_4058_);
v_a_boxed_4068_ = lean_unbox(v_a_4059_);
v_res_4069_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_4056_, v_type_4057_, v_report_boxed_4067_, v_a_boxed_4068_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
uint8_t v_a_boxed_4079_; lean_object* v_res_4080_; 
v_a_boxed_4079_ = lean_unbox(v_a_4071_);
v_res_4080_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_4070_, v_a_boxed_4079_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___boxed(lean_object* v_upperBound_4081_, lean_object* v___x_4082_, lean_object* v_f_4083_, lean_object* v___x_4084_, lean_object* v_a_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v___y_69484__boxed_4095_; lean_object* v_res_4096_; 
v___y_69484__boxed_4095_ = lean_unbox(v___y_4087_);
v_res_4096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4081_, v___x_4082_, v_f_4083_, v___x_4084_, v_a_4085_, v_b_4086_, v___y_69484__boxed_4095_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec_ref(v___x_4084_);
lean_dec_ref(v_f_4083_);
lean_dec(v___x_4082_);
lean_dec(v_upperBound_4081_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_4097_, lean_object* v_prop_4098_, lean_object* v_h_4099_, lean_object* v_e_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
uint8_t v_a_boxed_4109_; lean_object* v_res_4110_; 
v_a_boxed_4109_ = lean_unbox(v_a_4101_);
v_res_4110_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_4097_, v_prop_4098_, v_h_4099_, v_e_4100_, v_a_boxed_4109_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
uint8_t v_a_boxed_4120_; lean_object* v_res_4121_; 
v_a_boxed_4120_ = lean_unbox(v_a_4112_);
v_res_4121_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_4111_, v_a_boxed_4120_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_a_4116_);
lean_dec_ref(v_a_4115_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13___boxed(lean_object* v_e_4122_, lean_object* v_x_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v___y_69660__boxed_4134_; lean_object* v_res_4135_; 
v___y_69660__boxed_4134_ = lean_unbox(v___y_4126_);
v_res_4135_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__13(v_e_4122_, v_x_4123_, v_x_4124_, v_x_4125_, v___y_69660__boxed_4134_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_4136_ = _args[0];
lean_object* v_snd_4137_ = _args[1];
lean_object* v_a_4138_ = _args[2];
lean_object* v___x_4139_ = _args[3];
lean_object* v_fst_4140_ = _args[4];
lean_object* v_f_4141_ = _args[5];
lean_object* v___x_4142_ = _args[6];
lean_object* v___x_4143_ = _args[7];
lean_object* v___x_4144_ = _args[8];
lean_object* v_____r_4145_ = _args[9];
lean_object* v___y_4146_ = _args[10];
lean_object* v___y_4147_ = _args[11];
lean_object* v___y_4148_ = _args[12];
lean_object* v___y_4149_ = _args[13];
lean_object* v___y_4150_ = _args[14];
lean_object* v___y_4151_ = _args[15];
lean_object* v___y_4152_ = _args[16];
lean_object* v___y_4153_ = _args[17];
_start:
{
uint8_t v___x_69753__boxed_4154_; uint8_t v___y_69758__boxed_4155_; lean_object* v_res_4156_; 
v___x_69753__boxed_4154_ = lean_unbox(v___x_4139_);
v___y_69758__boxed_4155_ = lean_unbox(v___y_4146_);
v_res_4156_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg___lam__0(v___x_4136_, v_snd_4137_, v_a_4138_, v___x_69753__boxed_4154_, v_fst_4140_, v_f_4141_, v___x_4142_, v___x_4143_, v___x_4144_, v_____r_4145_, v___y_69758__boxed_4155_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec_ref(v___x_4144_);
lean_dec_ref(v___x_4143_);
lean_dec(v___x_4142_);
lean_dec_ref(v_f_4141_);
lean_dec(v_a_4138_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
uint8_t v_a_boxed_4166_; lean_object* v_res_4167_; 
v_a_boxed_4166_ = lean_unbox(v_a_4158_);
v_res_4167_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4157_, v_a_boxed_4166_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_4168_, uint8_t v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_4168_, v___y_4175_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v___y_72487__boxed_4187_; lean_object* v_res_4188_; 
v___y_72487__boxed_4187_ = lean_unbox(v___y_4179_);
v_res_4188_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_4178_, v___y_72487__boxed_4187_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(lean_object* v_declName_4189_, uint8_t v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___redArg(v_declName_4189_, v___y_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9___boxed(lean_object* v_declName_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v___y_72513__boxed_4208_; lean_object* v_res_4209_; 
v___y_72513__boxed_4208_ = lean_unbox(v___y_4200_);
v_res_4209_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__9(v_declName_4199_, v___y_72513__boxed_4208_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27(lean_object* v_00_u03b1_4210_, lean_object* v_name_4211_, lean_object* v_type_4212_, lean_object* v_val_4213_, lean_object* v_k_4214_, uint8_t v_nondep_4215_, uint8_t v_kind_4216_, uint8_t v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___redArg(v_name_4211_, v_type_4212_, v_val_4213_, v_k_4214_, v_nondep_4215_, v_kind_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27___boxed(lean_object* v_00_u03b1_4226_, lean_object* v_name_4227_, lean_object* v_type_4228_, lean_object* v_val_4229_, lean_object* v_k_4230_, lean_object* v_nondep_4231_, lean_object* v_kind_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
uint8_t v_nondep_boxed_4241_; uint8_t v_kind_boxed_4242_; uint8_t v___y_72539__boxed_4243_; lean_object* v_res_4244_; 
v_nondep_boxed_4241_ = lean_unbox(v_nondep_4231_);
v_kind_boxed_4242_ = lean_unbox(v_kind_4232_);
v___y_72539__boxed_4243_ = lean_unbox(v___y_4233_);
v_res_4244_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__27(v_00_u03b1_4226_, v_name_4227_, v_type_4228_, v_val_4229_, v_k_4230_, v_nondep_boxed_4241_, v_kind_boxed_4242_, v___y_72539__boxed_4243_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30(lean_object* v_00_u03b1_4245_, lean_object* v_name_4246_, uint8_t v_bi_4247_, lean_object* v_type_4248_, lean_object* v_k_4249_, uint8_t v_kind_4250_, uint8_t v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___redArg(v_name_4246_, v_bi_4247_, v_type_4248_, v_k_4249_, v_kind_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30___boxed(lean_object* v_00_u03b1_4260_, lean_object* v_name_4261_, lean_object* v_bi_4262_, lean_object* v_type_4263_, lean_object* v_k_4264_, lean_object* v_kind_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v_bi_boxed_4274_; uint8_t v_kind_boxed_4275_; uint8_t v___y_72565__boxed_4276_; lean_object* v_res_4277_; 
v_bi_boxed_4274_ = lean_unbox(v_bi_4262_);
v_kind_boxed_4275_ = lean_unbox(v_kind_4265_);
v___y_72565__boxed_4276_ = lean_unbox(v___y_4266_);
v_res_4277_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__30(v_00_u03b1_4260_, v_name_4261_, v_bi_boxed_4274_, v_type_4263_, v_k_4264_, v_kind_boxed_4275_, v___y_72565__boxed_4276_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_4278_, lean_object* v_m_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_4279_, v_a_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_4282_, lean_object* v_m_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_4282_, v_m_4283_, v_a_4284_);
lean_dec_ref(v_a_4284_);
lean_dec_ref(v_m_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_4286_, lean_object* v_m_4287_, lean_object* v_a_4288_, lean_object* v_b_4289_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_4287_, v_a_4288_, v_b_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_cls_4291_, lean_object* v_msg_4292_, uint8_t v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___redArg(v_cls_4291_, v_msg_4292_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_cls_4302_, lean_object* v_msg_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
uint8_t v___y_72595__boxed_4312_; lean_object* v_res_4313_; 
v___y_72595__boxed_4312_ = lean_unbox(v___y_4304_);
v_res_4313_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_cls_4302_, v_msg_4303_, v___y_72595__boxed_4312_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(lean_object* v_upperBound_4314_, lean_object* v___x_4315_, lean_object* v_f_4316_, lean_object* v___x_4317_, lean_object* v_inst_4318_, lean_object* v_R_4319_, lean_object* v_a_4320_, lean_object* v_b_4321_, lean_object* v_c_4322_, uint8_t v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___redArg(v_upperBound_4314_, v___x_4315_, v_f_4316_, v___x_4317_, v_a_4320_, v_b_4321_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_4332_ = _args[0];
lean_object* v___x_4333_ = _args[1];
lean_object* v_f_4334_ = _args[2];
lean_object* v___x_4335_ = _args[3];
lean_object* v_inst_4336_ = _args[4];
lean_object* v_R_4337_ = _args[5];
lean_object* v_a_4338_ = _args[6];
lean_object* v_b_4339_ = _args[7];
lean_object* v_c_4340_ = _args[8];
lean_object* v___y_4341_ = _args[9];
lean_object* v___y_4342_ = _args[10];
lean_object* v___y_4343_ = _args[11];
lean_object* v___y_4344_ = _args[12];
lean_object* v___y_4345_ = _args[13];
lean_object* v___y_4346_ = _args[14];
lean_object* v___y_4347_ = _args[15];
lean_object* v___y_4348_ = _args[16];
_start:
{
uint8_t v___y_72625__boxed_4349_; lean_object* v_res_4350_; 
v___y_72625__boxed_4349_ = lean_unbox(v___y_4341_);
v_res_4350_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__12(v_upperBound_4332_, v___x_4333_, v_f_4334_, v___x_4335_, v_inst_4336_, v_R_4337_, v_a_4338_, v_b_4339_, v_c_4340_, v___y_72625__boxed_4349_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec_ref(v___x_4335_);
lean_dec_ref(v_f_4334_);
lean_dec(v___x_4333_);
lean_dec(v_upperBound_4332_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11(lean_object* v_00_u03b2_4351_, lean_object* v_a_4352_, lean_object* v_x_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___redArg(v_a_4352_, v_x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11___boxed(lean_object* v_00_u03b2_4355_, lean_object* v_a_4356_, lean_object* v_x_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__11(v_00_u03b2_4355_, v_a_4356_, v_x_4357_);
lean_dec(v_x_4357_);
lean_dec_ref(v_a_4356_);
return v_res_4358_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_4359_, lean_object* v_a_4360_, lean_object* v_x_4361_){
_start:
{
uint8_t v___x_4362_; 
v___x_4362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_a_4360_, v_x_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___boxed(lean_object* v_00_u03b2_4363_, lean_object* v_a_4364_, lean_object* v_x_4365_){
_start:
{
uint8_t v_res_4366_; lean_object* v_r_4367_; 
v_res_4366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(v_00_u03b2_4363_, v_a_4364_, v_x_4365_);
lean_dec(v_x_4365_);
lean_dec_ref(v_a_4364_);
v_r_4367_ = lean_box(v_res_4366_);
return v_r_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_4368_, lean_object* v_data_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_data_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15(lean_object* v_00_u03b2_4371_, lean_object* v_a_4372_, lean_object* v_b_4373_, lean_object* v_x_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__15___redArg(v_a_4372_, v_b_4373_, v_x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31(lean_object* v_00_u03b2_4376_, lean_object* v_i_4377_, lean_object* v_source_4378_, lean_object* v_target_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31___redArg(v_i_4377_, v_source_4378_, v_target_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36(lean_object* v_00_u03b2_4381_, lean_object* v_x_4382_, lean_object* v_x_4383_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14_spec__31_spec__36___redArg(v_x_4382_, v_x_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_4385_, lean_object* v_i_4386_, lean_object* v_arg_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_4385_, v_i_4386_, v_arg_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4409_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4409_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4409_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
uint8_t v___x_4398_; 
v___x_4398_ = lean_unbox(v_a_4394_);
lean_dec(v_a_4394_);
if (v___x_4398_ == 3)
{
uint8_t v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4399_ = 0;
v___x_4400_ = lean_box(v___x_4399_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4400_);
v___x_4402_ = v___x_4396_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
else
{
uint8_t v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = 1;
v___x_4405_ = lean_box(v___x_4404_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4405_);
v___x_4407_ = v___x_4396_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
v_a_4410_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4393_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4393_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_4418_, lean_object* v_i_4419_, lean_object* v_arg_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_4418_, v_i_4419_, v_arg_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
lean_dec(v_i_4419_);
lean_dec_ref(v_pinfos_4418_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_4427_, lean_object* v_opts_4428_, lean_object* v_act_4429_, lean_object* v_decl_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
lean_inc(v___y_4432_);
lean_inc_ref(v___y_4431_);
v___x_4438_ = lean_apply_6(v_act_4429_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
v___x_4439_ = l_Lean_profileitIOUnsafe___redArg(v_category_4427_, v_opts_4428_, v___x_4438_, v_decl_4430_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_4440_, lean_object* v_opts_4441_, lean_object* v_act_4442_, lean_object* v_decl_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4440_, v_opts_4441_, v_act_4442_, v_decl_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec_ref(v_opts_4441_);
lean_dec_ref(v_category_4440_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_4452_, lean_object* v_category_4453_, lean_object* v_opts_4454_, lean_object* v_act_4455_, lean_object* v_decl_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v___x_4464_; 
v___x_4464_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_4453_, v_opts_4454_, v_act_4455_, v_decl_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_4465_, lean_object* v_category_4466_, lean_object* v_opts_4467_, lean_object* v_act_4468_, lean_object* v_decl_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_4465_, v_category_4466_, v_opts_4467_, v_act_4468_, v_decl_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec_ref(v_opts_4467_);
lean_dec_ref(v_category_4466_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_4478_, lean_object* v_e_4479_, uint8_t v___x_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___y_4489_; lean_object* v___x_4498_; uint8_t v_transparency_4499_; uint8_t v___x_4500_; 
v___x_4498_ = l_Lean_Meta_Context_config(v___y_4483_);
v_transparency_4499_ = lean_ctor_get_uint8(v___x_4498_, 9);
lean_dec_ref(v___x_4498_);
v___x_4500_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4499_, v___x_4478_);
if (v___x_4500_ == 0)
{
lean_object* v_keyedConfig_4501_; uint8_t v_trackZetaDelta_4502_; lean_object* v_zetaDeltaSet_4503_; lean_object* v_lctx_4504_; lean_object* v_localInstances_4505_; lean_object* v_defEqCtx_x3f_4506_; lean_object* v_synthPendingDepth_4507_; lean_object* v_customCanUnfoldPredicate_x3f_4508_; uint8_t v_univApprox_4509_; uint8_t v_inTypeClassResolution_4510_; uint8_t v_cacheInferType_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_keyedConfig_4501_ = lean_ctor_get(v___y_4483_, 0);
v_trackZetaDelta_4502_ = lean_ctor_get_uint8(v___y_4483_, sizeof(void*)*7);
v_zetaDeltaSet_4503_ = lean_ctor_get(v___y_4483_, 1);
v_lctx_4504_ = lean_ctor_get(v___y_4483_, 2);
v_localInstances_4505_ = lean_ctor_get(v___y_4483_, 3);
v_defEqCtx_x3f_4506_ = lean_ctor_get(v___y_4483_, 4);
v_synthPendingDepth_4507_ = lean_ctor_get(v___y_4483_, 5);
v_customCanUnfoldPredicate_x3f_4508_ = lean_ctor_get(v___y_4483_, 6);
v_univApprox_4509_ = lean_ctor_get_uint8(v___y_4483_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4510_ = lean_ctor_get_uint8(v___y_4483_, sizeof(void*)*7 + 2);
v_cacheInferType_4511_ = lean_ctor_get_uint8(v___y_4483_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4501_);
v___x_4512_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4478_, v_keyedConfig_4501_);
lean_inc(v_customCanUnfoldPredicate_x3f_4508_);
lean_inc(v_synthPendingDepth_4507_);
lean_inc(v_defEqCtx_x3f_4506_);
lean_inc_ref(v_localInstances_4505_);
lean_inc_ref(v_lctx_4504_);
lean_inc(v_zetaDeltaSet_4503_);
v___x_4513_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
lean_ctor_set(v___x_4513_, 1, v_zetaDeltaSet_4503_);
lean_ctor_set(v___x_4513_, 2, v_lctx_4504_);
lean_ctor_set(v___x_4513_, 3, v_localInstances_4505_);
lean_ctor_set(v___x_4513_, 4, v_defEqCtx_x3f_4506_);
lean_ctor_set(v___x_4513_, 5, v_synthPendingDepth_4507_);
lean_ctor_set(v___x_4513_, 6, v_customCanUnfoldPredicate_x3f_4508_);
lean_ctor_set_uint8(v___x_4513_, sizeof(void*)*7, v_trackZetaDelta_4502_);
lean_ctor_set_uint8(v___x_4513_, sizeof(void*)*7 + 1, v_univApprox_4509_);
lean_ctor_set_uint8(v___x_4513_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4510_);
lean_ctor_set_uint8(v___x_4513_, sizeof(void*)*7 + 3, v_cacheInferType_4511_);
v___x_4514_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4479_, v___x_4480_, v___y_4481_, v___y_4482_, v___x_4513_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec_ref_known(v___x_4513_, 7);
v___y_4489_ = v___x_4514_;
goto v___jp_4488_;
}
else
{
lean_object* v___x_4515_; 
v___x_4515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_4479_, v___x_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
v___y_4489_ = v___x_4515_;
goto v___jp_4488_;
}
v___jp_4488_:
{
if (lean_obj_tag(v___y_4489_) == 0)
{
return v___y_4489_;
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_a_4490_ = lean_ctor_get(v___y_4489_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___y_4489_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___y_4489_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___y_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_4516_, lean_object* v_e_4517_, lean_object* v___x_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v___x_2117__boxed_4526_; uint8_t v___x_2118__boxed_4527_; lean_object* v_res_4528_; 
v___x_2117__boxed_4526_ = lean_unbox(v___x_4516_);
v___x_2118__boxed_4527_ = lean_unbox(v___x_4518_);
v_res_4528_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2117__boxed_4526_, v_e_4517_, v___x_2118__boxed_4527_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___f_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4538_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4535_);
v___x_4539_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_4540_ = 0;
v___x_4541_ = 2;
v___x_4542_ = lean_box(v___x_4541_);
v___x_4543_ = lean_box(v___x_4540_);
v___f_4544_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4544_, 0, v___x_4542_);
lean_closure_set(v___f_4544_, 1, v_e_4530_);
lean_closure_set(v___f_4544_, 2, v___x_4543_);
v___x_4545_ = lean_box(0);
v___x_4546_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_4539_, v___x_4538_, v___f_4544_, v___x_4545_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
lean_dec_ref(v___x_4538_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_Meta_Sym_canon(v_e_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
return v_res_4555_;
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

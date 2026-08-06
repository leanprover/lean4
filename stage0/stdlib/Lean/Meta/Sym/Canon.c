// Lean compiler output
// Module: Lean.Meta.Sym.Canon
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ExprPtr import Lean.Meta.SynthInstance import Lean.Meta.Sym.SynthInstance import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters import Lean.Meta.Sym.Eta import Lean.Meta.WHNF import Init.Grind.Util
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
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
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_105_; lean_object* v___y_106_; uint8_t v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_111_, v___y_113_);
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
v___y_105_ = v___y_110_;
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
v___y_110_ = v_modified_141_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_args_140_;
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
v___y_110_ = v_modified_141_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_args_140_;
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
v___x_256_ = lean_st_ref_set(v_a_204_, v___x_255_);
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
v___x_311_ = lean_st_ref_set(v_a_204_, v___x_310_);
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
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v_dummy_585_; 
v___x_584_ = lean_box(0);
v_dummy_585_ = l_Lean_Expr_sort___override(v___x_584_);
return v_dummy_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_586_, lean_object* v_e_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
uint8_t v_fromClass_593_; 
v_fromClass_593_ = lean_ctor_get_uint8(v_info_586_, sizeof(void*)*3);
if (v_fromClass_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_587_, v_fromClass_593_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_630_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_630_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_630_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_630_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_a_595_) == 1)
{
lean_object* v_val_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_del_object(v___x_597_);
v_val_599_ = lean_ctor_get(v_a_595_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v_a_595_, 1);
v___x_600_ = l_Lean_Expr_getAppFn(v_val_599_);
v___x_601_ = l_Lean_Meta_reduceProj_x3f(v___x_600_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
if (lean_obj_tag(v_a_602_) == 0)
{
lean_dec(v_val_599_);
return v___x_601_;
}
else
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_625_);
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_624_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_624_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_623_; 
v_val_606_ = lean_ctor_get(v_a_602_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_623_ == 0)
{
v___x_608_ = v_a_602_;
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v_a_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_dummy_610_; lean_object* v_nargs_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v_dummy_610_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_611_ = l_Lean_Expr_getAppNumArgs(v_val_599_);
lean_inc(v_nargs_611_);
v___x_612_ = lean_mk_array(v_nargs_611_, v_dummy_610_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_sub(v_nargs_611_, v___x_613_);
lean_dec(v_nargs_611_);
v___x_615_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_599_, v___x_612_, v___x_614_);
v___x_616_ = l_Lean_mkAppN(v_val_606_, v___x_615_);
lean_dec_ref(v___x_615_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_616_);
v___x_618_ = v___x_608_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_622_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_618_);
v___x_620_ = v___x_604_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
else
{
lean_dec(v_val_599_);
return v___x_601_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_dec(v_a_595_);
v___x_626_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_626_);
v___x_628_ = v___x_597_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
return v___x_594_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v_e_587_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_633_, lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_633_, v_e_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec_ref(v_info_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_641_, lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_641_, v_e_642_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_651_, lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_651_, v_e_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec_ref(v_info_651_);
return v_res_660_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_661_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_663_ = l_Lean_Expr_isConstOf(v_e_661_, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_664_);
lean_dec_ref(v_e_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = l_Lean_Expr_cleanupAnnotations(v_e_700_);
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_703_ = l_Lean_Expr_isConstOf(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Expr_isApp(v___x_701_);
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_707_ = l_Lean_Expr_isConstOf(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = l_Lean_Expr_isApp(v___x_705_);
if (v___x_708_ == 0)
{
lean_dec_ref(v___x_705_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = l_Lean_Expr_appFnCleanup___redArg(v___x_705_);
v___x_710_ = l_Lean_Expr_isApp(v___x_709_);
if (v___x_710_ == 0)
{
lean_dec_ref(v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_709_);
v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_711_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
v___x_714_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_714_ == 0)
{
lean_dec_ref(v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
v___x_716_ = l_Lean_Expr_isApp(v___x_715_);
if (v___x_716_ == 0)
{
lean_dec_ref(v___x_715_);
return v___x_716_;
}
else
{
lean_object* v_arg_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_arg_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc_ref(v_arg_717_);
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_715_);
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_720_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_722_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_724_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_726_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_728_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_727_);
lean_dec_ref(v___x_718_);
if (v___x_728_ == 0)
{
lean_dec_ref(v_arg_717_);
return v___x_728_;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_717_);
lean_dec_ref(v_arg_717_);
return v___x_729_;
}
}
else
{
uint8_t v___x_730_; 
lean_dec_ref(v___x_718_);
v___x_730_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_717_);
lean_dec_ref(v_arg_717_);
return v___x_730_;
}
}
else
{
uint8_t v___x_731_; 
lean_dec_ref(v___x_718_);
v___x_731_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_717_);
lean_dec_ref(v_arg_717_);
return v___x_731_;
}
}
else
{
uint8_t v___x_732_; 
lean_dec_ref(v___x_718_);
v___x_732_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_717_);
lean_dec_ref(v_arg_717_);
return v___x_732_;
}
}
else
{
uint8_t v___x_733_; 
lean_dec_ref(v___x_718_);
v___x_733_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_717_);
lean_dec_ref(v_arg_717_);
return v___x_733_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_705_);
return v___x_707_;
}
}
}
else
{
lean_dec_ref(v___x_701_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_734_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_743_, lean_object* v_inst_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
lean_inc_ref(v_inst_744_);
lean_inc_ref(v_e_743_);
v___x_752_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_743_, v_inst_744_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_803_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_803_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_803_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_803_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
uint8_t v___x_757_; 
v___x_757_ = lean_unbox(v_a_753_);
lean_dec(v_a_753_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_del_object(v___x_755_);
v___x_758_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_745_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_791_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_791_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v_verbose_763_; 
v_verbose_763_ = lean_ctor_get_uint8(v_a_759_, 0);
lean_dec(v_a_759_);
if (v_verbose_763_ == 0)
{
lean_object* v___x_765_; 
lean_dec_ref(v_inst_744_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_e_743_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_e_743_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_del_object(v___x_761_);
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_743_);
v___x_768_ = l_Lean_indentExpr(v_e_743_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_indentExpr(v_inst_744_);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Meta_Sym_reportIssue(v___x_773_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_782_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_e_743_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_e_743_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_e_743_);
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_inst_744_);
lean_dec_ref(v_e_743_);
v_a_792_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_758_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_758_);
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
lean_object* v___x_801_; 
lean_dec_ref(v_e_743_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_inst_744_);
v___x_801_ = v___x_755_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_inst_744_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_inst_744_);
lean_dec_ref(v_e_743_);
v_a_804_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_752_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_752_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_812_, lean_object* v_inst_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_812_, v_inst_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_env_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_st_ref_get(v___y_823_);
v_env_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc_ref(v_env_826_);
lean_dec(v___x_825_);
v___x_827_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_826_, v_declName_822_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_829_, v___y_830_);
lean_dec(v___y_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_833_, uint8_t v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_833_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___y_4015__boxed_852_; lean_object* v_res_853_; 
v___y_4015__boxed_852_ = lean_unbox(v___y_844_);
v_res_853_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_843_, v___y_4015__boxed_852_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_854_, uint8_t v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
uint8_t v___x_863_; 
lean_inc_ref(v_e_854_);
v___x_863_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_854_);
if (v___x_863_ == 0)
{
lean_object* v_f_864_; 
v_f_864_ = l_Lean_Expr_getAppFn(v_e_854_);
if (lean_obj_tag(v_f_864_) == 4)
{
lean_object* v_declName_865_; lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_896_; 
v_declName_865_ = lean_ctor_get(v_f_864_, 0);
lean_inc(v_declName_865_);
lean_dec_ref_known(v_f_864_, 2);
v___x_866_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_865_, v_a_861_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_896_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_896_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_896_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_872_; 
lean_del_object(v___x_869_);
v_val_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_a_867_, 1);
lean_inc_ref(v_e_854_);
v___x_872_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_871_, v_e_854_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_val_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_884_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_884_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
if (lean_obj_tag(v_a_873_) == 0)
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_e_854_);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_e_854_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v_val_880_; lean_object* v___x_882_; 
lean_dec_ref(v_e_854_);
v_val_880_ = lean_ctor_get(v_a_873_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_a_873_, 1);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_val_880_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_val_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_e_854_);
v_a_885_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_872_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_872_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_e_854_);
v___x_894_ = v___x_869_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_e_854_);
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
lean_object* v___x_897_; 
lean_dec_ref(v_f_864_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_e_854_);
return v___x_897_;
}
}
else
{
lean_object* v___x_898_; 
lean_inc_ref(v_e_854_);
v___x_898_ = l_Lean_Meta_evalNat(v_e_854_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_929_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_929_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_929_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_929_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
if (lean_obj_tag(v_a_899_) == 1)
{
lean_object* v_val_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec_ref(v_e_854_);
v_val_903_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v_a_899_, 1);
v___x_904_ = l_Lean_mkNatLit(v_val_903_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v___x_908_; 
lean_del_object(v___x_901_);
lean_dec(v_a_899_);
lean_inc_ref(v_e_854_);
v___x_908_ = l_Lean_Meta_isOffset_x3f(v_e_854_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_920_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_920_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
if (lean_obj_tag(v_a_909_) == 1)
{
lean_object* v_val_913_; lean_object* v_fst_914_; lean_object* v_snd_915_; lean_object* v___x_916_; 
lean_del_object(v___x_911_);
lean_dec_ref(v_e_854_);
v_val_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v_a_909_, 1);
v_fst_914_ = lean_ctor_get(v_val_913_, 0);
lean_inc(v_fst_914_);
v_snd_915_ = lean_ctor_get(v_val_913_, 1);
lean_inc(v_snd_915_);
lean_dec(v_val_913_);
v___x_916_ = l_Lean_Meta_mkOffset(v_fst_914_, v_snd_915_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_916_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_854_);
v___x_918_ = v___x_911_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_e_854_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_e_854_);
v_a_921_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_908_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_908_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
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
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v_e_854_);
v_a_930_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_898_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_898_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
uint8_t v_a_boxed_947_; lean_object* v_res_948_; 
v_a_boxed_947_ = lean_unbox(v_a_939_);
v_res_948_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_938_, v_a_boxed_947_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_952_, lean_object* v_type_953_, uint8_t v_report_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; 
lean_inc_ref(v_type_953_);
v___x_962_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_953_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1014_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_1014_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1014_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
if (lean_obj_tag(v_a_963_) == 1)
{
lean_object* v_val_967_; lean_object* v___x_968_; 
lean_del_object(v___x_965_);
lean_dec_ref(v_type_953_);
v_val_967_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v_a_963_, 1);
v___x_968_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_952_, v_val_967_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
return v___x_968_;
}
else
{
lean_dec(v_a_963_);
if (v_report_954_ == 0)
{
lean_object* v___x_970_; 
lean_dec_ref(v_type_953_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_e_952_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_e_952_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_972_; 
lean_del_object(v___x_965_);
v___x_972_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_955_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1005_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1005_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1005_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
uint8_t v_verbose_977_; 
v_verbose_977_ = lean_ctor_get_uint8(v_a_973_, 0);
lean_dec(v_a_973_);
if (v_verbose_977_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v_type_953_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_e_952_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_e_952_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_del_object(v___x_975_);
v___x_981_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_952_);
v___x_982_ = l_Lean_indentExpr(v_e_952_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Lean_indentExpr(v_type_953_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_Meta_Sym_reportIssue(v___x_987_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_988_, 0);
lean_dec(v_unused_996_);
v___x_990_ = v___x_988_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_dec(v___x_988_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_e_952_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_e_952_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v_e_952_);
v_a_997_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_988_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
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
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v_type_953_);
lean_dec_ref(v_e_952_);
v_a_1006_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_972_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_972_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_type_953_);
lean_dec_ref(v_e_952_);
v_a_1015_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_962_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_962_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1023_, lean_object* v_type_1024_, lean_object* v_report_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_report_boxed_1033_; lean_object* v_res_1034_; 
v_report_boxed_1033_ = lean_unbox(v_report_1025_);
v_res_1034_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1023_, v_type_1024_, v_report_boxed_1033_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1035_, lean_object* v_type_1036_, uint8_t v_report_1037_, uint8_t v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1035_, v_type_1036_, v_report_1037_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1047_, lean_object* v_type_1048_, lean_object* v_report_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v_report_boxed_1058_; uint8_t v_a_boxed_1059_; lean_object* v_res_1060_; 
v_report_boxed_1058_ = lean_unbox(v_report_1049_);
v_a_boxed_1059_ = lean_unbox(v_a_1050_);
v_res_1060_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1047_, v_type_1048_, v_report_boxed_1058_, v_a_boxed_1059_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1060_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
uint8_t v___x_1063_; 
v___x_1063_ = 0;
return v___x_1063_;
}
else
{
lean_object* v_key_1064_; lean_object* v_tail_1065_; uint8_t v___x_1066_; 
v_key_1064_ = lean_ctor_get(v_x_1062_, 0);
v_tail_1065_ = lean_ctor_get(v_x_1062_, 2);
v___x_1066_ = lean_expr_eqv(v_key_1064_, v_a_1061_);
if (v___x_1066_ == 0)
{
v_x_1062_ = v_tail_1065_;
goto _start;
}
else
{
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1068_, lean_object* v_x_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1068_, v_x_1069_);
lean_dec(v_x_1069_);
lean_dec_ref(v_a_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
return v_x_1072_;
}
else
{
lean_object* v_key_1074_; lean_object* v_value_1075_; lean_object* v_tail_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1099_; 
v_key_1074_ = lean_ctor_get(v_x_1073_, 0);
v_value_1075_ = lean_ctor_get(v_x_1073_, 1);
v_tail_1076_ = lean_ctor_get(v_x_1073_, 2);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1078_ = v_x_1073_;
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_tail_1076_);
lean_inc(v_value_1075_);
lean_inc(v_key_1074_);
lean_dec(v_x_1073_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v_fold_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1080_ = lean_array_get_size(v_x_1072_);
v___x_1081_ = l_Lean_Expr_hash(v_key_1074_);
v___x_1082_ = 32ULL;
v___x_1083_ = lean_uint64_shift_right(v___x_1081_, v___x_1082_);
v_fold_1084_ = lean_uint64_xor(v___x_1081_, v___x_1083_);
v___x_1085_ = 16ULL;
v___x_1086_ = lean_uint64_shift_right(v_fold_1084_, v___x_1085_);
v___x_1087_ = lean_uint64_xor(v_fold_1084_, v___x_1086_);
v___x_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = lean_usize_of_nat(v___x_1080_);
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_sub(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_usize_land(v___x_1088_, v___x_1091_);
v___x_1093_ = lean_array_uget_borrowed(v_x_1072_, v___x_1092_);
lean_inc(v___x_1093_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 2, v___x_1093_);
v___x_1095_ = v___x_1078_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_key_1074_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_value_1075_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_array_uset(v_x_1072_, v___x_1092_, v___x_1095_);
v_x_1072_ = v___x_1096_;
v_x_1073_ = v_tail_1076_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object* v_i_1100_, lean_object* v_source_1101_, lean_object* v_target_1102_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_array_get_size(v_source_1101_);
v___x_1104_ = lean_nat_dec_lt(v_i_1100_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v_source_1101_);
lean_dec(v_i_1100_);
return v_target_1102_;
}
else
{
lean_object* v_es_1105_; lean_object* v___x_1106_; lean_object* v_source_1107_; lean_object* v_target_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_es_1105_ = lean_array_fget(v_source_1101_, v_i_1100_);
v___x_1106_ = lean_box(0);
v_source_1107_ = lean_array_fset(v_source_1101_, v_i_1100_, v___x_1106_);
v_target_1108_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_1102_, v_es_1105_);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_add(v_i_1100_, v___x_1109_);
lean_dec(v_i_1100_);
v_i_1100_ = v___x_1110_;
v_source_1101_ = v_source_1107_;
v_target_1102_ = v_target_1108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v_nbuckets_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1113_ = lean_array_get_size(v_data_1112_);
v___x_1114_ = lean_unsigned_to_nat(2u);
v_nbuckets_1115_ = lean_nat_mul(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_mk_array(v_nbuckets_1115_, v___x_1117_);
v___x_1119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_1116_, v_data_1112_, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1120_, lean_object* v_b_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_dec(v_b_1121_);
lean_dec_ref(v_a_1120_);
return v_x_1122_;
}
else
{
lean_object* v_key_1123_; lean_object* v_value_1124_; lean_object* v_tail_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
v_key_1123_ = lean_ctor_get(v_x_1122_, 0);
v_value_1124_ = lean_ctor_get(v_x_1122_, 1);
v_tail_1125_ = lean_ctor_get(v_x_1122_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v_x_1122_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_tail_1125_);
lean_inc(v_value_1124_);
lean_inc(v_key_1123_);
lean_dec(v_x_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_expr_eqv(v_key_1123_, v_a_1120_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1120_, v_b_1121_, v_tail_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 2, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_key_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_value_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1135_; 
lean_dec(v_value_1124_);
lean_dec(v_key_1123_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v_b_1121_);
lean_ctor_set(v___x_1127_, 0, v_a_1120_);
v___x_1135_ = v___x_1127_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1120_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_b_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_tail_1125_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1138_, lean_object* v_a_1139_, lean_object* v_b_1140_){
_start:
{
lean_object* v_size_1141_; lean_object* v_buckets_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1185_; 
v_size_1141_ = lean_ctor_get(v_m_1138_, 0);
v_buckets_1142_ = lean_ctor_get(v_m_1138_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_m_1138_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1144_ = v_m_1138_;
v_isShared_1145_ = v_isSharedCheck_1185_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_buckets_1142_);
lean_inc(v_size_1141_);
lean_dec(v_m_1138_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1185_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v_fold_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; lean_object* v_bkt_1159_; uint8_t v___x_1160_; 
v___x_1146_ = lean_array_get_size(v_buckets_1142_);
v___x_1147_ = l_Lean_Expr_hash(v_a_1139_);
v___x_1148_ = 32ULL;
v___x_1149_ = lean_uint64_shift_right(v___x_1147_, v___x_1148_);
v_fold_1150_ = lean_uint64_xor(v___x_1147_, v___x_1149_);
v___x_1151_ = 16ULL;
v___x_1152_ = lean_uint64_shift_right(v_fold_1150_, v___x_1151_);
v___x_1153_ = lean_uint64_xor(v_fold_1150_, v___x_1152_);
v___x_1154_ = lean_uint64_to_usize(v___x_1153_);
v___x_1155_ = lean_usize_of_nat(v___x_1146_);
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_sub(v___x_1155_, v___x_1156_);
v___x_1158_ = lean_usize_land(v___x_1154_, v___x_1157_);
v_bkt_1159_ = lean_array_uget_borrowed(v_buckets_1142_, v___x_1158_);
v___x_1160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1139_, v_bkt_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v_size_x27_1162_; lean_object* v___x_1163_; lean_object* v_buckets_x27_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v_size_x27_1162_ = lean_nat_add(v_size_1141_, v___x_1161_);
lean_dec(v_size_1141_);
lean_inc(v_bkt_1159_);
v___x_1163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1163_, 0, v_a_1139_);
lean_ctor_set(v___x_1163_, 1, v_b_1140_);
lean_ctor_set(v___x_1163_, 2, v_bkt_1159_);
v_buckets_x27_1164_ = lean_array_uset(v_buckets_1142_, v___x_1158_, v___x_1163_);
v___x_1165_ = lean_unsigned_to_nat(4u);
v___x_1166_ = lean_nat_mul(v_size_x27_1162_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(3u);
v___x_1168_ = lean_nat_div(v___x_1166_, v___x_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_array_get_size(v_buckets_x27_1164_);
v___x_1170_ = lean_nat_dec_le(v___x_1168_, v___x_1169_);
lean_dec(v___x_1168_);
if (v___x_1170_ == 0)
{
lean_object* v_val_1171_; lean_object* v___x_1173_; 
v_val_1171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1164_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_val_1171_);
lean_ctor_set(v___x_1144_, 0, v_size_x27_1162_);
v___x_1173_ = v___x_1144_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_size_x27_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_val_1171_);
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
lean_object* v___x_1176_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_buckets_x27_1164_);
lean_ctor_set(v___x_1144_, 0, v_size_x27_1162_);
v___x_1176_ = v___x_1144_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_size_x27_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_buckets_x27_1164_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v___x_1178_; lean_object* v_buckets_x27_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_inc(v_bkt_1159_);
v___x_1178_ = lean_box(0);
v_buckets_x27_1179_ = lean_array_uset(v_buckets_1142_, v___x_1158_, v___x_1178_);
v___x_1180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1139_, v_b_1140_, v_bkt_1159_);
v___x_1181_ = lean_array_uset(v_buckets_x27_1179_, v___x_1158_, v___x_1180_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1181_);
v___x_1183_ = v___x_1144_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_size_1141_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1181_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object* v_k_1186_, uint8_t v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_box(v___y_1187_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___x_1197_ = lean_apply_9(v_k_1186_, v_b_1190_, v___x_1196_, v___y_1188_, v___y_1189_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, lean_box(0));
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object* v_k_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v_b_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v___y_66738__boxed_1208_; lean_object* v_res_1209_; 
v___y_66738__boxed_1208_ = lean_unbox(v___y_1199_);
v_res_1209_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1198_, v___y_66738__boxed_1208_, v___y_1200_, v___y_1201_, v_b_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object* v_name_1210_, uint8_t v_bi_1211_, lean_object* v_type_1212_, lean_object* v_k_1213_, uint8_t v_kind_1214_, uint8_t v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_box(v___y_1215_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1224_, 0, v_k_1213_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v___y_1216_);
lean_closure_set(v___f_1224_, 3, v___y_1217_);
v___x_1225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1210_, v_bi_1211_, v_type_1212_, v___f_1224_, v_kind_1214_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object* v_name_1234_, lean_object* v_bi_1235_, lean_object* v_type_1236_, lean_object* v_k_1237_, lean_object* v_kind_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_bi_boxed_1247_; uint8_t v_kind_boxed_1248_; uint8_t v___y_66766__boxed_1249_; lean_object* v_res_1250_; 
v_bi_boxed_1247_ = lean_unbox(v_bi_1235_);
v_kind_boxed_1248_ = lean_unbox(v_kind_1238_);
v___y_66766__boxed_1249_ = lean_unbox(v___y_1239_);
v_res_1250_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1234_, v_bi_boxed_1247_, v_type_1236_, v_k_1237_, v_kind_boxed_1248_, v___y_66766__boxed_1249_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; lean_object* v_env_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = lean_st_ref_get(v___y_1252_);
v_env_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_ref(v_env_1255_);
lean_dec(v___x_1254_);
v___x_1256_ = l_Lean_Meta_isMatcherCore(v_env_1255_, v_declName_1251_);
v___x_1257_ = lean_box(v___x_1256_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1259_, v___y_1260_);
lean_dec(v___y_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object* v_msgData_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v_env_1270_; lean_object* v___x_1271_; lean_object* v_mctx_1272_; lean_object* v_lctx_1273_; lean_object* v_options_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1269_ = lean_st_ref_get(v___y_1267_);
v_env_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_env_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_st_ref_get(v___y_1265_);
v_mctx_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc_ref(v_mctx_1272_);
lean_dec(v___x_1271_);
v_lctx_1273_ = lean_ctor_get(v___y_1264_, 2);
v_options_1274_ = lean_ctor_get(v___y_1266_, 2);
lean_inc_ref(v_options_1274_);
lean_inc_ref(v_lctx_1273_);
v___x_1275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1275_, 0, v_env_1270_);
lean_ctor_set(v___x_1275_, 1, v_mctx_1272_);
lean_ctor_set(v___x_1275_, 2, v_lctx_1273_);
lean_ctor_set(v___x_1275_, 3, v_options_1274_);
v___x_1276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_msgData_1263_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object* v_msgData_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1285_; double v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_float_of_nat(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_cls_1290_, lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_ref_1297_; lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1343_; 
v_ref_1297_ = lean_ctor_get(v___y_1294_, 5);
v___x_1298_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_traceState_1304_; lean_object* v_env_1305_; lean_object* v_nextMacroScope_1306_; lean_object* v_ngen_1307_; lean_object* v_auxDeclNGen_1308_; lean_object* v_cache_1309_; lean_object* v_messages_1310_; lean_object* v_infoState_1311_; lean_object* v_snapshotTasks_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1342_; 
v___x_1303_ = lean_st_ref_take(v___y_1295_);
v_traceState_1304_ = lean_ctor_get(v___x_1303_, 4);
v_env_1305_ = lean_ctor_get(v___x_1303_, 0);
v_nextMacroScope_1306_ = lean_ctor_get(v___x_1303_, 1);
v_ngen_1307_ = lean_ctor_get(v___x_1303_, 2);
v_auxDeclNGen_1308_ = lean_ctor_get(v___x_1303_, 3);
v_cache_1309_ = lean_ctor_get(v___x_1303_, 5);
v_messages_1310_ = lean_ctor_get(v___x_1303_, 6);
v_infoState_1311_ = lean_ctor_get(v___x_1303_, 7);
v_snapshotTasks_1312_ = lean_ctor_get(v___x_1303_, 8);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1314_ = v___x_1303_;
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_snapshotTasks_1312_);
lean_inc(v_infoState_1311_);
lean_inc(v_messages_1310_);
lean_inc(v_cache_1309_);
lean_inc(v_traceState_1304_);
lean_inc(v_auxDeclNGen_1308_);
lean_inc(v_ngen_1307_);
lean_inc(v_nextMacroScope_1306_);
lean_inc(v_env_1305_);
lean_dec(v___x_1303_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
uint64_t v_tid_1316_; lean_object* v_traces_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1341_; 
v_tid_1316_ = lean_ctor_get_uint64(v_traceState_1304_, sizeof(void*)*1);
v_traces_1317_ = lean_ctor_get(v_traceState_1304_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_traceState_1304_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1319_ = v_traceState_1304_;
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_traces_1317_);
lean_dec(v_traceState_1304_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; double v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1323_ = 0;
v___x_1324_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1325_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1325_, 0, v_cls_1290_);
lean_ctor_set(v___x_1325_, 1, v___x_1321_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
lean_ctor_set_float(v___x_1325_, sizeof(void*)*3, v___x_1322_);
lean_ctor_set_float(v___x_1325_, sizeof(void*)*3 + 8, v___x_1322_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*3 + 16, v___x_1323_);
v___x_1326_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1327_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v_a_1299_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
lean_inc(v_ref_1297_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_ref_1297_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_PersistentArray_push___redArg(v_traces_1317_, v___x_1328_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1329_);
v___x_1331_ = v___x_1319_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1329_);
lean_ctor_set_uint64(v_reuseFailAlloc_1340_, sizeof(void*)*1, v_tid_1316_);
v___x_1331_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v___x_1331_);
v___x_1333_ = v___x_1314_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_env_1305_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_nextMacroScope_1306_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_ngen_1307_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_auxDeclNGen_1308_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_cache_1309_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_messages_1310_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_infoState_1311_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_snapshotTasks_1312_);
v___x_1333_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = lean_st_ref_set(v___y_1295_, v___x_1333_);
v___x_1335_ = lean_box(0);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1335_);
v___x_1337_ = v___x_1301_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1344_, lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1344_, v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1352_, lean_object* v_x_1353_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_box(0);
return v___x_1354_;
}
else
{
lean_object* v_key_1355_; lean_object* v_value_1356_; lean_object* v_tail_1357_; uint8_t v___x_1358_; 
v_key_1355_ = lean_ctor_get(v_x_1353_, 0);
v_value_1356_ = lean_ctor_get(v_x_1353_, 1);
v_tail_1357_ = lean_ctor_get(v_x_1353_, 2);
v___x_1358_ = lean_expr_eqv(v_key_1355_, v_a_1352_);
if (v___x_1358_ == 0)
{
v_x_1353_ = v_tail_1357_;
goto _start;
}
else
{
lean_object* v___x_1360_; 
lean_inc(v_value_1356_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_value_1356_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1361_, v_x_1362_);
lean_dec(v_x_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_buckets_1366_; lean_object* v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; uint64_t v_fold_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_buckets_1366_ = lean_ctor_get(v_m_1364_, 1);
v___x_1367_ = lean_array_get_size(v_buckets_1366_);
v___x_1368_ = l_Lean_Expr_hash(v_a_1365_);
v___x_1369_ = 32ULL;
v___x_1370_ = lean_uint64_shift_right(v___x_1368_, v___x_1369_);
v_fold_1371_ = lean_uint64_xor(v___x_1368_, v___x_1370_);
v___x_1372_ = 16ULL;
v___x_1373_ = lean_uint64_shift_right(v_fold_1371_, v___x_1372_);
v___x_1374_ = lean_uint64_xor(v_fold_1371_, v___x_1373_);
v___x_1375_ = lean_uint64_to_usize(v___x_1374_);
v___x_1376_ = lean_usize_of_nat(v___x_1367_);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_sub(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_usize_land(v___x_1375_, v___x_1378_);
v___x_1380_ = lean_array_uget_borrowed(v_buckets_1366_, v___x_1379_);
v___x_1381_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1365_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1382_, v_a_1383_);
lean_dec_ref(v_a_1383_);
lean_dec_ref(v_m_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1385_, lean_object* v_type_1386_, lean_object* v_val_1387_, lean_object* v_k_1388_, uint8_t v_nondep_1389_, uint8_t v_kind_1390_, uint8_t v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(v___y_1391_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
v___f_1400_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1400_, 0, v_k_1388_);
lean_closure_set(v___f_1400_, 1, v___x_1399_);
lean_closure_set(v___f_1400_, 2, v___y_1392_);
lean_closure_set(v___f_1400_, 3, v___y_1393_);
v___x_1401_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1385_, v_type_1386_, v_val_1387_, v___f_1400_, v_nondep_1389_, v_kind_1390_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
return v___x_1401_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1410_, lean_object* v_type_1411_, lean_object* v_val_1412_, lean_object* v_k_1413_, lean_object* v_nondep_1414_, lean_object* v_kind_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_nondep_boxed_1424_; uint8_t v_kind_boxed_1425_; uint8_t v___y_67001__boxed_1426_; lean_object* v_res_1427_; 
v_nondep_boxed_1424_ = lean_unbox(v_nondep_1414_);
v_kind_boxed_1425_ = lean_unbox(v_kind_1415_);
v___y_67001__boxed_1426_ = lean_unbox(v___y_1416_);
v_res_1427_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1410_, v_type_1411_, v_val_1412_, v_k_1413_, v_nondep_boxed_1424_, v_kind_boxed_1425_, v___y_67001__boxed_1426_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = l_Lean_instInhabitedExpr;
v___x_1430_ = lean_panic_fn_borrowed(v___x_1429_, v_msg_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1433_, lean_object* v_body_1434_, lean_object* v_x_1435_, uint8_t v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_array_push(v_fvars_1433_, v_x_1435_);
v___x_1445_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1444_, v_body_1434_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1446_, lean_object* v_body_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v___y_67164__boxed_1457_; lean_object* v_res_1458_; 
v___y_67164__boxed_1457_ = lean_unbox(v___y_1449_);
v_res_1458_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1446_, v_body_1447_, v_x_1448_, v___y_67164__boxed_1457_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1459_, lean_object* v_e_1460_, uint8_t v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
if (lean_obj_tag(v_e_1460_) == 6)
{
lean_object* v_binderName_1469_; lean_object* v_binderType_1470_; lean_object* v_body_1471_; uint8_t v_binderInfo_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_binderName_1469_ = lean_ctor_get(v_e_1460_, 0);
lean_inc(v_binderName_1469_);
v_binderType_1470_ = lean_ctor_get(v_e_1460_, 1);
lean_inc_ref(v_binderType_1470_);
v_body_1471_ = lean_ctor_get(v_e_1460_, 2);
lean_inc_ref(v_body_1471_);
v_binderInfo_1472_ = lean_ctor_get_uint8(v_e_1460_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1473_ = lean_expr_instantiate_rev(v_binderType_1470_, v_fvars_1459_);
lean_dec_ref(v_binderType_1470_);
v___x_1474_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1473_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___f_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___f_1476_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1476_, 0, v_fvars_1459_);
lean_closure_set(v___f_1476_, 1, v_body_1471_);
v___x_1477_ = 0;
v___x_1478_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1469_, v_binderInfo_1472_, v_a_1475_, v___f_1476_, v___x_1477_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1478_;
}
else
{
lean_dec_ref(v_body_1471_);
lean_dec(v_binderName_1469_);
lean_dec_ref(v_fvars_1459_);
return v___x_1474_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_expr_instantiate_rev(v_e_1460_, v_fvars_1459_);
lean_dec_ref(v_e_1460_);
v___x_1480_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1479_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; uint8_t v___x_1482_; uint8_t v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = 0;
v___x_1483_ = 1;
v___x_1484_ = 1;
v___x_1485_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1459_, v_a_1481_, v___x_1482_, v___x_1483_, v___x_1482_, v___x_1483_, v___x_1484_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec_ref(v_fvars_1459_);
return v___x_1485_;
}
else
{
lean_dec_ref(v_fvars_1459_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1486_, uint8_t v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
if (v_a_1487_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1496_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1495_, v_e_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1498_ = l_Lean_Meta_Sym_etaReduce(v_e_1486_);
lean_dec_ref(v_e_1486_);
v___x_1499_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1497_, v___x_1498_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1500_, lean_object* v_body_1501_, lean_object* v_x_1502_, uint8_t v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_array_push(v_fvars_1500_, v_x_1502_);
v___x_1512_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1511_, v_body_1501_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1513_, lean_object* v_body_1514_, lean_object* v_x_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v___y_67175__boxed_1524_; lean_object* v_res_1525_; 
v___y_67175__boxed_1524_ = lean_unbox(v___y_1516_);
v_res_1525_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1513_, v_body_1514_, v_x_1515_, v___y_67175__boxed_1524_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1526_, lean_object* v_e_1527_, uint8_t v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
if (lean_obj_tag(v_e_1527_) == 8)
{
lean_object* v_declName_1536_; lean_object* v_type_1537_; lean_object* v_value_1538_; lean_object* v_body_1539_; uint8_t v_nondep_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_declName_1536_ = lean_ctor_get(v_e_1527_, 0);
lean_inc(v_declName_1536_);
v_type_1537_ = lean_ctor_get(v_e_1527_, 1);
lean_inc_ref(v_type_1537_);
v_value_1538_ = lean_ctor_get(v_e_1527_, 2);
lean_inc_ref(v_value_1538_);
v_body_1539_ = lean_ctor_get(v_e_1527_, 3);
lean_inc_ref(v_body_1539_);
v_nondep_1540_ = lean_ctor_get_uint8(v_e_1527_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1527_, 4);
v___x_1541_ = lean_expr_instantiate_rev(v_type_1537_, v_fvars_1526_);
lean_dec_ref(v_type_1537_);
v___x_1542_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1541_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_expr_instantiate_rev(v_value_1538_, v_fvars_1526_);
lean_dec_ref(v_value_1538_);
v___x_1545_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1544_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___f_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___f_1547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1547_, 0, v_fvars_1526_);
lean_closure_set(v___f_1547_, 1, v_body_1539_);
v___x_1548_ = 0;
v___x_1549_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1536_, v_a_1543_, v_a_1546_, v___f_1547_, v_nondep_1540_, v___x_1548_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
return v___x_1549_;
}
else
{
lean_dec(v_a_1543_);
lean_dec_ref(v_body_1539_);
lean_dec(v_declName_1536_);
lean_dec_ref(v_fvars_1526_);
return v___x_1545_;
}
}
else
{
lean_dec_ref(v_body_1539_);
lean_dec_ref(v_value_1538_);
lean_dec(v_declName_1536_);
lean_dec_ref(v_fvars_1526_);
return v___x_1542_;
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_expr_instantiate_rev(v_e_1527_, v_fvars_1526_);
lean_dec_ref(v_e_1527_);
v___x_1551_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1550_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; uint8_t v___x_1553_; uint8_t v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = 1;
v___x_1554_ = 0;
v___x_1555_ = 1;
v___x_1556_ = l_Lean_Meta_mkLetFVars(v_fvars_1526_, v_a_1552_, v___x_1553_, v___x_1554_, v___x_1555_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec_ref(v_fvars_1526_);
return v___x_1556_;
}
else
{
lean_dec_ref(v_fvars_1526_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1557_, uint8_t v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
if (v_a_1558_ == 0)
{
uint8_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = 1;
v___x_1567_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1557_, v___x_1566_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1569_, uint8_t v_report_1570_, uint8_t v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; 
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc_ref(v_e_1569_);
v___x_1579_ = lean_infer_type(v_e_1569_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_n(v_a_1580_, 2);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_Meta_isProp(v_a_1580_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1594_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
if (v_a_1571_ == 0)
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1590_ == 0)
{
lean_del_object(v___x_1584_);
goto v___jp_1586_;
}
else
{
lean_object* v___x_1592_; 
lean_dec(v_a_1580_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_e_1569_);
v___x_1592_ = v___x_1584_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_e_1569_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_del_object(v___x_1584_);
lean_dec(v_a_1582_);
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1580_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1569_, v_a_1588_, v_report_1570_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_1589_;
}
else
{
lean_dec_ref(v_e_1569_);
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1580_);
lean_dec_ref(v_e_1569_);
v_a_1595_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1581_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1581_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_dec_ref(v_e_1569_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1603_, uint8_t v_report_1604_, uint8_t v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
if (v_a_1605_ == 0)
{
lean_object* v___x_1613_; lean_object* v_canon_1614_; lean_object* v_cache_1615_; lean_object* v___x_1616_; 
v___x_1613_ = lean_st_ref_get(v_a_1607_);
v_canon_1614_ = lean_ctor_get(v___x_1613_, 9);
lean_inc_ref(v_canon_1614_);
lean_dec(v___x_1613_);
v_cache_1615_ = lean_ctor_get(v_canon_1614_, 0);
lean_inc_ref(v_cache_1615_);
lean_dec_ref(v_canon_1614_);
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1615_, v_e_1603_);
lean_dec_ref(v_cache_1615_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_e_1603_);
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_val_1617_);
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
lean_ctor_set_tag(v___x_1619_, 0);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_val_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v___x_1625_; 
lean_dec(v___x_1616_);
lean_inc_ref(v_e_1603_);
v___x_1625_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1603_, v_report_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1664_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1664_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1664_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v_canon_1631_; lean_object* v_share_1632_; lean_object* v_maxFVar_1633_; lean_object* v_proofInstInfo_1634_; lean_object* v_inferType_1635_; lean_object* v_getLevel_1636_; lean_object* v_congrInfo_1637_; lean_object* v_defEqI_1638_; lean_object* v_extensions_1639_; lean_object* v_issues_1640_; lean_object* v_instanceOverrides_1641_; uint8_t v_debug_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1663_; 
v___x_1630_ = lean_st_ref_take(v_a_1607_);
v_canon_1631_ = lean_ctor_get(v___x_1630_, 9);
v_share_1632_ = lean_ctor_get(v___x_1630_, 0);
v_maxFVar_1633_ = lean_ctor_get(v___x_1630_, 1);
v_proofInstInfo_1634_ = lean_ctor_get(v___x_1630_, 2);
v_inferType_1635_ = lean_ctor_get(v___x_1630_, 3);
v_getLevel_1636_ = lean_ctor_get(v___x_1630_, 4);
v_congrInfo_1637_ = lean_ctor_get(v___x_1630_, 5);
v_defEqI_1638_ = lean_ctor_get(v___x_1630_, 6);
v_extensions_1639_ = lean_ctor_get(v___x_1630_, 7);
v_issues_1640_ = lean_ctor_get(v___x_1630_, 8);
v_instanceOverrides_1641_ = lean_ctor_get(v___x_1630_, 10);
v_debug_1642_ = lean_ctor_get_uint8(v___x_1630_, sizeof(void*)*11);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1644_ = v___x_1630_;
v_isShared_1645_ = v_isSharedCheck_1663_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_instanceOverrides_1641_);
lean_inc(v_canon_1631_);
lean_inc(v_issues_1640_);
lean_inc(v_extensions_1639_);
lean_inc(v_defEqI_1638_);
lean_inc(v_congrInfo_1637_);
lean_inc(v_getLevel_1636_);
lean_inc(v_inferType_1635_);
lean_inc(v_proofInstInfo_1634_);
lean_inc(v_maxFVar_1633_);
lean_inc(v_share_1632_);
lean_dec(v___x_1630_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1663_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_cache_1646_; lean_object* v_cacheInType_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1662_; 
v_cache_1646_ = lean_ctor_get(v_canon_1631_, 0);
v_cacheInType_1647_ = lean_ctor_get(v_canon_1631_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_canon_1631_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1649_ = v_canon_1631_;
v_isShared_1650_ = v_isSharedCheck_1662_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_cacheInType_1647_);
lean_inc(v_cache_1646_);
lean_dec(v_canon_1631_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1662_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_inc(v_a_1626_);
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1646_, v_e_1603_, v_a_1626_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_cacheInType_1647_);
v___x_1653_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 9, v___x_1653_);
v___x_1655_ = v___x_1644_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_share_1632_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_maxFVar_1633_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_proofInstInfo_1634_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_inferType_1635_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_getLevel_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v_congrInfo_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 6, v_defEqI_1638_);
lean_ctor_set(v_reuseFailAlloc_1660_, 7, v_extensions_1639_);
lean_ctor_set(v_reuseFailAlloc_1660_, 8, v_issues_1640_);
lean_ctor_set(v_reuseFailAlloc_1660_, 9, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 10, v_instanceOverrides_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11, v_debug_1642_);
v___x_1655_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_st_ref_set(v_a_1607_, v___x_1655_);
if (v_isShared_1629_ == 0)
{
v___x_1658_ = v___x_1628_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1626_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1603_);
return v___x_1625_;
}
}
}
else
{
lean_object* v___x_1665_; lean_object* v_canon_1666_; lean_object* v_cacheInType_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_st_ref_get(v_a_1607_);
v_canon_1666_ = lean_ctor_get(v___x_1665_, 9);
lean_inc_ref(v_canon_1666_);
lean_dec(v___x_1665_);
v_cacheInType_1667_ = lean_ctor_get(v_canon_1666_, 1);
lean_inc_ref(v_cacheInType_1667_);
lean_dec_ref(v_canon_1666_);
v___x_1668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1667_, v_e_1603_);
lean_dec_ref(v_cacheInType_1667_);
if (lean_obj_tag(v___x_1668_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v_e_1603_);
v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_val_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 0);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_val_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v___x_1677_; 
lean_dec(v___x_1668_);
lean_inc_ref(v_e_1603_);
v___x_1677_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1603_, v_report_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1716_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1716_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1716_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v_canon_1683_; lean_object* v_share_1684_; lean_object* v_maxFVar_1685_; lean_object* v_proofInstInfo_1686_; lean_object* v_inferType_1687_; lean_object* v_getLevel_1688_; lean_object* v_congrInfo_1689_; lean_object* v_defEqI_1690_; lean_object* v_extensions_1691_; lean_object* v_issues_1692_; lean_object* v_instanceOverrides_1693_; uint8_t v_debug_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1715_; 
v___x_1682_ = lean_st_ref_take(v_a_1607_);
v_canon_1683_ = lean_ctor_get(v___x_1682_, 9);
v_share_1684_ = lean_ctor_get(v___x_1682_, 0);
v_maxFVar_1685_ = lean_ctor_get(v___x_1682_, 1);
v_proofInstInfo_1686_ = lean_ctor_get(v___x_1682_, 2);
v_inferType_1687_ = lean_ctor_get(v___x_1682_, 3);
v_getLevel_1688_ = lean_ctor_get(v___x_1682_, 4);
v_congrInfo_1689_ = lean_ctor_get(v___x_1682_, 5);
v_defEqI_1690_ = lean_ctor_get(v___x_1682_, 6);
v_extensions_1691_ = lean_ctor_get(v___x_1682_, 7);
v_issues_1692_ = lean_ctor_get(v___x_1682_, 8);
v_instanceOverrides_1693_ = lean_ctor_get(v___x_1682_, 10);
v_debug_1694_ = lean_ctor_get_uint8(v___x_1682_, sizeof(void*)*11);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1696_ = v___x_1682_;
v_isShared_1697_ = v_isSharedCheck_1715_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_instanceOverrides_1693_);
lean_inc(v_canon_1683_);
lean_inc(v_issues_1692_);
lean_inc(v_extensions_1691_);
lean_inc(v_defEqI_1690_);
lean_inc(v_congrInfo_1689_);
lean_inc(v_getLevel_1688_);
lean_inc(v_inferType_1687_);
lean_inc(v_proofInstInfo_1686_);
lean_inc(v_maxFVar_1685_);
lean_inc(v_share_1684_);
lean_dec(v___x_1682_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1715_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_cache_1698_; lean_object* v_cacheInType_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1714_; 
v_cache_1698_ = lean_ctor_get(v_canon_1683_, 0);
v_cacheInType_1699_ = lean_ctor_get(v_canon_1683_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_canon_1683_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1701_ = v_canon_1683_;
v_isShared_1702_ = v_isSharedCheck_1714_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_cacheInType_1699_);
lean_inc(v_cache_1698_);
lean_dec(v_canon_1683_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1714_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
lean_inc(v_a_1678_);
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1699_, v_e_1603_, v_a_1678_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_cache_1698_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 9, v___x_1705_);
v___x_1707_ = v___x_1696_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_share_1684_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_maxFVar_1685_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_proofInstInfo_1686_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_inferType_1687_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_getLevel_1688_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_congrInfo_1689_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_defEqI_1690_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_extensions_1691_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_issues_1692_);
lean_ctor_set(v_reuseFailAlloc_1712_, 9, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 10, v_instanceOverrides_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*11, v_debug_1694_);
v___x_1707_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_st_ref_set(v_a_1607_, v___x_1707_);
if (v_isShared_1681_ == 0)
{
v___x_1710_ = v___x_1680_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1678_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1603_);
return v___x_1677_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1733_ = l_Lean_mkConst(v___x_1732_, v___x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1734_, lean_object* v_prop_1735_, lean_object* v_inst_1736_, lean_object* v_e_1737_, uint8_t v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
lean_inc_ref(v_prop_1735_);
v___x_1746_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1735_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1786_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1786_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1786_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___y_1752_; uint8_t v___y_1753_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1747_);
v___x_1762_ = l_Lean_Expr_app___override(v___x_1761_, v_a_1747_);
if (v_a_1738_ == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1762_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___y_1766_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_inc_ref(v_inst_1736_);
v___y_1766_ = v_inst_1736_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1775_; 
v_val_1775_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v_a_1764_, 1);
v___y_1766_ = v_val_1775_;
goto v___jp_1765_;
}
v___jp_1765_:
{
lean_object* v___x_1767_; 
lean_inc_ref(v_inst_1736_);
v___x_1767_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1736_, v___y_1766_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; size_t v___x_1769_; size_t v___x_1770_; uint8_t v___x_1771_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = lean_ptr_addr(v_prop_1735_);
lean_dec_ref(v_prop_1735_);
v___x_1770_ = lean_ptr_addr(v_a_1747_);
v___x_1771_ = lean_usize_dec_eq(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v_inst_1736_);
v___y_1752_ = v_a_1768_;
v___y_1753_ = v___x_1771_;
goto v___jp_1751_;
}
else
{
size_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_ptr_addr(v_inst_1736_);
lean_dec_ref(v_inst_1736_);
v___x_1773_ = lean_ptr_addr(v_a_1768_);
v___x_1774_ = lean_usize_dec_eq(v___x_1772_, v___x_1773_);
v___y_1752_ = v_a_1768_;
v___y_1753_ = v___x_1774_;
goto v___jp_1751_;
}
}
else
{
lean_del_object(v___x_1749_);
lean_dec(v_a_1747_);
lean_dec_ref(v_e_1737_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_prop_1735_);
lean_dec_ref(v_g_1734_);
return v___x_1767_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1749_);
lean_dec(v_a_1747_);
lean_dec_ref(v_e_1737_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_prop_1735_);
lean_dec_ref(v_g_1734_);
v_a_1776_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1763_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1763_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
uint8_t v___x_1784_; lean_object* v___x_1785_; 
lean_del_object(v___x_1749_);
lean_dec(v_a_1747_);
lean_dec_ref(v_e_1737_);
lean_dec_ref(v_prop_1735_);
lean_dec_ref(v_g_1734_);
v___x_1784_ = 0;
v___x_1785_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1736_, v___x_1762_, v___x_1784_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1785_;
}
v___jp_1751_:
{
if (v___y_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec_ref(v_e_1737_);
v___x_1754_ = l_Lean_mkAppB(v_g_1734_, v_a_1747_, v___y_1752_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1754_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
else
{
lean_object* v___x_1759_; 
lean_dec_ref(v___y_1752_);
lean_dec(v_a_1747_);
lean_dec_ref(v_g_1734_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v_e_1737_);
v___x_1759_ = v___x_1749_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_e_1737_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1737_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_prop_1735_);
lean_dec_ref(v_g_1734_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1787_, lean_object* v_prop_1788_, lean_object* v_h_1789_, lean_object* v_e_1790_, uint8_t v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
if (v_a_1791_ == 0)
{
lean_object* v___x_1799_; lean_object* v_canon_1800_; lean_object* v_cache_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_st_ref_get(v_a_1793_);
v_canon_1800_ = lean_ctor_get(v___x_1799_, 9);
lean_inc_ref(v_canon_1800_);
lean_dec(v___x_1799_);
v_cache_1801_ = lean_ctor_get(v_canon_1800_, 0);
lean_inc_ref(v_cache_1801_);
lean_dec_ref(v_canon_1800_);
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1801_, v_e_1790_);
lean_dec_ref(v_cache_1801_);
if (lean_obj_tag(v___x_1802_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_e_1790_);
lean_dec_ref(v_h_1789_);
lean_dec_ref(v_prop_1788_);
lean_dec_ref(v_g_1787_);
v_val_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_val_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 0);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_val_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1811_; 
lean_dec(v___x_1802_);
lean_inc_ref(v_e_1790_);
v___x_1811_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1787_, v_prop_1788_, v_h_1789_, v_e_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1850_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1850_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1850_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v_canon_1817_; lean_object* v_share_1818_; lean_object* v_maxFVar_1819_; lean_object* v_proofInstInfo_1820_; lean_object* v_inferType_1821_; lean_object* v_getLevel_1822_; lean_object* v_congrInfo_1823_; lean_object* v_defEqI_1824_; lean_object* v_extensions_1825_; lean_object* v_issues_1826_; lean_object* v_instanceOverrides_1827_; uint8_t v_debug_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1849_; 
v___x_1816_ = lean_st_ref_take(v_a_1793_);
v_canon_1817_ = lean_ctor_get(v___x_1816_, 9);
v_share_1818_ = lean_ctor_get(v___x_1816_, 0);
v_maxFVar_1819_ = lean_ctor_get(v___x_1816_, 1);
v_proofInstInfo_1820_ = lean_ctor_get(v___x_1816_, 2);
v_inferType_1821_ = lean_ctor_get(v___x_1816_, 3);
v_getLevel_1822_ = lean_ctor_get(v___x_1816_, 4);
v_congrInfo_1823_ = lean_ctor_get(v___x_1816_, 5);
v_defEqI_1824_ = lean_ctor_get(v___x_1816_, 6);
v_extensions_1825_ = lean_ctor_get(v___x_1816_, 7);
v_issues_1826_ = lean_ctor_get(v___x_1816_, 8);
v_instanceOverrides_1827_ = lean_ctor_get(v___x_1816_, 10);
v_debug_1828_ = lean_ctor_get_uint8(v___x_1816_, sizeof(void*)*11);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1830_ = v___x_1816_;
v_isShared_1831_ = v_isSharedCheck_1849_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_instanceOverrides_1827_);
lean_inc(v_canon_1817_);
lean_inc(v_issues_1826_);
lean_inc(v_extensions_1825_);
lean_inc(v_defEqI_1824_);
lean_inc(v_congrInfo_1823_);
lean_inc(v_getLevel_1822_);
lean_inc(v_inferType_1821_);
lean_inc(v_proofInstInfo_1820_);
lean_inc(v_maxFVar_1819_);
lean_inc(v_share_1818_);
lean_dec(v___x_1816_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1849_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_cache_1832_; lean_object* v_cacheInType_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1848_; 
v_cache_1832_ = lean_ctor_get(v_canon_1817_, 0);
v_cacheInType_1833_ = lean_ctor_get(v_canon_1817_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_canon_1817_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1835_ = v_canon_1817_;
v_isShared_1836_ = v_isSharedCheck_1848_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_cacheInType_1833_);
lean_inc(v_cache_1832_);
lean_dec(v_canon_1817_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1848_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_inc(v_a_1812_);
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1832_, v_e_1790_, v_a_1812_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_cacheInType_1833_);
v___x_1839_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 9, v___x_1839_);
v___x_1841_ = v___x_1830_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_share_1818_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_maxFVar_1819_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_proofInstInfo_1820_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_inferType_1821_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_getLevel_1822_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_congrInfo_1823_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_defEqI_1824_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_extensions_1825_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_issues_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 9, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 10, v_instanceOverrides_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, sizeof(void*)*11, v_debug_1828_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_st_ref_set(v_a_1793_, v___x_1841_);
if (v_isShared_1815_ == 0)
{
v___x_1844_ = v___x_1814_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1812_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1790_);
return v___x_1811_;
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v_canon_1852_; lean_object* v_cacheInType_1853_; lean_object* v___x_1854_; 
v___x_1851_ = lean_st_ref_get(v_a_1793_);
v_canon_1852_ = lean_ctor_get(v___x_1851_, 9);
lean_inc_ref(v_canon_1852_);
lean_dec(v___x_1851_);
v_cacheInType_1853_ = lean_ctor_get(v_canon_1852_, 1);
lean_inc_ref(v_cacheInType_1853_);
lean_dec_ref(v_canon_1852_);
v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1853_, v_e_1790_);
lean_dec_ref(v_cacheInType_1853_);
if (lean_obj_tag(v___x_1854_) == 1)
{
lean_object* v_val_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_e_1790_);
lean_dec_ref(v_h_1789_);
lean_dec_ref(v_prop_1788_);
lean_dec_ref(v_g_1787_);
v_val_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_val_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 0);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_val_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v___x_1863_; 
lean_dec(v___x_1854_);
lean_inc_ref(v_e_1790_);
v___x_1863_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1787_, v_prop_1788_, v_h_1789_, v_e_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1902_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1902_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1902_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v_canon_1869_; lean_object* v_share_1870_; lean_object* v_maxFVar_1871_; lean_object* v_proofInstInfo_1872_; lean_object* v_inferType_1873_; lean_object* v_getLevel_1874_; lean_object* v_congrInfo_1875_; lean_object* v_defEqI_1876_; lean_object* v_extensions_1877_; lean_object* v_issues_1878_; lean_object* v_instanceOverrides_1879_; uint8_t v_debug_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1901_; 
v___x_1868_ = lean_st_ref_take(v_a_1793_);
v_canon_1869_ = lean_ctor_get(v___x_1868_, 9);
v_share_1870_ = lean_ctor_get(v___x_1868_, 0);
v_maxFVar_1871_ = lean_ctor_get(v___x_1868_, 1);
v_proofInstInfo_1872_ = lean_ctor_get(v___x_1868_, 2);
v_inferType_1873_ = lean_ctor_get(v___x_1868_, 3);
v_getLevel_1874_ = lean_ctor_get(v___x_1868_, 4);
v_congrInfo_1875_ = lean_ctor_get(v___x_1868_, 5);
v_defEqI_1876_ = lean_ctor_get(v___x_1868_, 6);
v_extensions_1877_ = lean_ctor_get(v___x_1868_, 7);
v_issues_1878_ = lean_ctor_get(v___x_1868_, 8);
v_instanceOverrides_1879_ = lean_ctor_get(v___x_1868_, 10);
v_debug_1880_ = lean_ctor_get_uint8(v___x_1868_, sizeof(void*)*11);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1882_ = v___x_1868_;
v_isShared_1883_ = v_isSharedCheck_1901_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_instanceOverrides_1879_);
lean_inc(v_canon_1869_);
lean_inc(v_issues_1878_);
lean_inc(v_extensions_1877_);
lean_inc(v_defEqI_1876_);
lean_inc(v_congrInfo_1875_);
lean_inc(v_getLevel_1874_);
lean_inc(v_inferType_1873_);
lean_inc(v_proofInstInfo_1872_);
lean_inc(v_maxFVar_1871_);
lean_inc(v_share_1870_);
lean_dec(v___x_1868_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1901_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_cache_1884_; lean_object* v_cacheInType_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1900_; 
v_cache_1884_ = lean_ctor_get(v_canon_1869_, 0);
v_cacheInType_1885_ = lean_ctor_get(v_canon_1869_, 1);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_canon_1869_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1887_ = v_canon_1869_;
v_isShared_1888_ = v_isSharedCheck_1900_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_cacheInType_1885_);
lean_inc(v_cache_1884_);
lean_dec(v_canon_1869_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1900_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_inc(v_a_1864_);
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1885_, v_e_1790_, v_a_1864_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_cache_1884_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 9, v___x_1891_);
v___x_1893_ = v___x_1882_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_share_1870_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_maxFVar_1871_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_proofInstInfo_1872_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_inferType_1873_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_getLevel_1874_);
lean_ctor_set(v_reuseFailAlloc_1898_, 5, v_congrInfo_1875_);
lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_defEqI_1876_);
lean_ctor_set(v_reuseFailAlloc_1898_, 7, v_extensions_1877_);
lean_ctor_set(v_reuseFailAlloc_1898_, 8, v_issues_1878_);
lean_ctor_set(v_reuseFailAlloc_1898_, 9, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1898_, 10, v_instanceOverrides_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*11, v_debug_1880_);
v___x_1893_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_st_ref_set(v_a_1793_, v___x_1893_);
if (v_isShared_1867_ == 0)
{
v___x_1896_ = v___x_1866_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1864_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1790_);
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1903_, lean_object* v_prop_1904_, lean_object* v_h_1905_, lean_object* v_e_1906_, uint8_t v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_a_1916_; lean_object* v___y_1950_; 
if (v_a_1907_ == 0)
{
lean_object* v___x_1990_; lean_object* v_canon_1991_; lean_object* v_cache_1992_; lean_object* v___x_1993_; 
v___x_1990_ = lean_st_ref_get(v_a_1909_);
v_canon_1991_ = lean_ctor_get(v___x_1990_, 9);
lean_inc_ref(v_canon_1991_);
lean_dec(v___x_1990_);
v_cache_1992_ = lean_ctor_get(v_canon_1991_, 0);
lean_inc_ref(v_cache_1992_);
lean_dec_ref(v_canon_1991_);
v___x_1993_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1992_, v_e_1906_);
lean_dec_ref(v_cache_1992_);
if (lean_obj_tag(v___x_1993_) == 1)
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_e_1906_);
lean_dec_ref(v_h_1905_);
lean_dec_ref(v_prop_1904_);
lean_dec_ref(v_g_1903_);
v_val_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 0);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v___x_1993_);
lean_inc_ref(v_prop_1904_);
v___x_2002_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1904_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_n(v_a_2003_, 2);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2003_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___y_2007_; uint8_t v___y_2008_; lean_object* v___y_2011_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
if (lean_obj_tag(v_a_2005_) == 0)
{
lean_inc_ref(v_h_1905_);
v___y_2011_ = v_h_1905_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2018_; 
v_val_2018_ = lean_ctor_get(v_a_2005_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v_a_2005_, 1);
v___y_2011_ = v_val_2018_;
goto v___jp_2010_;
}
v___jp_2006_:
{
if (v___y_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_mkAppB(v_g_1903_, v_a_2003_, v___y_2007_);
v_a_1916_ = v___x_2009_;
goto v___jp_1915_;
}
else
{
lean_dec_ref(v___y_2007_);
lean_dec(v_a_2003_);
lean_dec_ref(v_g_1903_);
lean_inc_ref(v_e_1906_);
v_a_1916_ = v_e_1906_;
goto v___jp_1915_;
}
}
v___jp_2010_:
{
size_t v___x_2012_; size_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_ptr_addr(v_prop_1904_);
lean_dec_ref(v_prop_1904_);
v___x_2013_ = lean_ptr_addr(v_a_2003_);
v___x_2014_ = lean_usize_dec_eq(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v_h_1905_);
v___y_2007_ = v___y_2011_;
v___y_2008_ = v___x_2014_;
goto v___jp_2006_;
}
else
{
size_t v___x_2015_; size_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = lean_ptr_addr(v_h_1905_);
lean_dec_ref(v_h_1905_);
v___x_2016_ = lean_ptr_addr(v___y_2011_);
v___x_2017_ = lean_usize_dec_eq(v___x_2015_, v___x_2016_);
v___y_2007_ = v___y_2011_;
v___y_2008_ = v___x_2017_;
goto v___jp_2006_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_a_2003_);
lean_dec_ref(v_e_1906_);
lean_dec_ref(v_h_1905_);
lean_dec_ref(v_prop_1904_);
lean_dec_ref(v_g_1903_);
v_a_2019_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2004_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2004_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_dec_ref(v_h_1905_);
lean_dec_ref(v_prop_1904_);
lean_dec_ref(v_g_1903_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2002_, 1);
v_a_1916_ = v_a_2027_;
goto v___jp_1915_;
}
else
{
lean_dec_ref(v_e_1906_);
return v___x_2002_;
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v_canon_2029_; lean_object* v_cacheInType_2030_; lean_object* v___x_2031_; 
lean_dec_ref(v_g_1903_);
v___x_2028_ = lean_st_ref_get(v_a_1909_);
v_canon_2029_ = lean_ctor_get(v___x_2028_, 9);
lean_inc_ref(v_canon_2029_);
lean_dec(v___x_2028_);
v_cacheInType_2030_ = lean_ctor_get(v_canon_2029_, 1);
lean_inc_ref(v_cacheInType_2030_);
lean_dec_ref(v_canon_2029_);
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2030_, v_e_1906_);
lean_dec_ref(v_cacheInType_2030_);
if (lean_obj_tag(v___x_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_e_1906_);
lean_dec_ref(v_h_1905_);
lean_dec_ref(v_prop_1904_);
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 0);
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_val_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v___x_2040_; 
lean_dec(v___x_2031_);
v___x_2040_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1904_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = 0;
v___x_2043_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1905_, v_a_2041_, v___x_2042_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
v___y_1950_ = v___x_2043_;
goto v___jp_1949_;
}
else
{
lean_dec_ref(v_h_1905_);
v___y_1950_ = v___x_2040_;
goto v___jp_1949_;
}
}
}
v___jp_1915_:
{
lean_object* v___x_1917_; lean_object* v_canon_1918_; lean_object* v_share_1919_; lean_object* v_maxFVar_1920_; lean_object* v_proofInstInfo_1921_; lean_object* v_inferType_1922_; lean_object* v_getLevel_1923_; lean_object* v_congrInfo_1924_; lean_object* v_defEqI_1925_; lean_object* v_extensions_1926_; lean_object* v_issues_1927_; lean_object* v_instanceOverrides_1928_; uint8_t v_debug_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1948_; 
v___x_1917_ = lean_st_ref_take(v_a_1909_);
v_canon_1918_ = lean_ctor_get(v___x_1917_, 9);
v_share_1919_ = lean_ctor_get(v___x_1917_, 0);
v_maxFVar_1920_ = lean_ctor_get(v___x_1917_, 1);
v_proofInstInfo_1921_ = lean_ctor_get(v___x_1917_, 2);
v_inferType_1922_ = lean_ctor_get(v___x_1917_, 3);
v_getLevel_1923_ = lean_ctor_get(v___x_1917_, 4);
v_congrInfo_1924_ = lean_ctor_get(v___x_1917_, 5);
v_defEqI_1925_ = lean_ctor_get(v___x_1917_, 6);
v_extensions_1926_ = lean_ctor_get(v___x_1917_, 7);
v_issues_1927_ = lean_ctor_get(v___x_1917_, 8);
v_instanceOverrides_1928_ = lean_ctor_get(v___x_1917_, 10);
v_debug_1929_ = lean_ctor_get_uint8(v___x_1917_, sizeof(void*)*11);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1931_ = v___x_1917_;
v_isShared_1932_ = v_isSharedCheck_1948_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_instanceOverrides_1928_);
lean_inc(v_canon_1918_);
lean_inc(v_issues_1927_);
lean_inc(v_extensions_1926_);
lean_inc(v_defEqI_1925_);
lean_inc(v_congrInfo_1924_);
lean_inc(v_getLevel_1923_);
lean_inc(v_inferType_1922_);
lean_inc(v_proofInstInfo_1921_);
lean_inc(v_maxFVar_1920_);
lean_inc(v_share_1919_);
lean_dec(v___x_1917_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1948_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_cache_1933_; lean_object* v_cacheInType_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1947_; 
v_cache_1933_ = lean_ctor_get(v_canon_1918_, 0);
v_cacheInType_1934_ = lean_ctor_get(v_canon_1918_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_canon_1918_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1936_ = v_canon_1918_;
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_cacheInType_1934_);
lean_inc(v_cache_1933_);
lean_dec(v_canon_1918_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_inc_ref(v_a_1916_);
v___x_1938_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1933_, v_e_1906_, v_a_1916_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_cacheInType_1934_);
v___x_1940_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 9, v___x_1940_);
v___x_1942_ = v___x_1931_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_share_1919_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_maxFVar_1920_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_proofInstInfo_1921_);
lean_ctor_set(v_reuseFailAlloc_1945_, 3, v_inferType_1922_);
lean_ctor_set(v_reuseFailAlloc_1945_, 4, v_getLevel_1923_);
lean_ctor_set(v_reuseFailAlloc_1945_, 5, v_congrInfo_1924_);
lean_ctor_set(v_reuseFailAlloc_1945_, 6, v_defEqI_1925_);
lean_ctor_set(v_reuseFailAlloc_1945_, 7, v_extensions_1926_);
lean_ctor_set(v_reuseFailAlloc_1945_, 8, v_issues_1927_);
lean_ctor_set(v_reuseFailAlloc_1945_, 9, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1945_, 10, v_instanceOverrides_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*11, v_debug_1929_);
v___x_1942_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_st_ref_set(v_a_1909_, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_a_1916_);
return v___x_1944_;
}
}
}
}
}
v___jp_1949_:
{
if (lean_obj_tag(v___y_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1989_; 
v_a_1951_ = lean_ctor_get(v___y_1950_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___y_1950_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1953_ = v___y_1950_;
v_isShared_1954_ = v_isSharedCheck_1989_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___y_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1989_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v_canon_1956_; lean_object* v_share_1957_; lean_object* v_maxFVar_1958_; lean_object* v_proofInstInfo_1959_; lean_object* v_inferType_1960_; lean_object* v_getLevel_1961_; lean_object* v_congrInfo_1962_; lean_object* v_defEqI_1963_; lean_object* v_extensions_1964_; lean_object* v_issues_1965_; lean_object* v_instanceOverrides_1966_; uint8_t v_debug_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1988_; 
v___x_1955_ = lean_st_ref_take(v_a_1909_);
v_canon_1956_ = lean_ctor_get(v___x_1955_, 9);
v_share_1957_ = lean_ctor_get(v___x_1955_, 0);
v_maxFVar_1958_ = lean_ctor_get(v___x_1955_, 1);
v_proofInstInfo_1959_ = lean_ctor_get(v___x_1955_, 2);
v_inferType_1960_ = lean_ctor_get(v___x_1955_, 3);
v_getLevel_1961_ = lean_ctor_get(v___x_1955_, 4);
v_congrInfo_1962_ = lean_ctor_get(v___x_1955_, 5);
v_defEqI_1963_ = lean_ctor_get(v___x_1955_, 6);
v_extensions_1964_ = lean_ctor_get(v___x_1955_, 7);
v_issues_1965_ = lean_ctor_get(v___x_1955_, 8);
v_instanceOverrides_1966_ = lean_ctor_get(v___x_1955_, 10);
v_debug_1967_ = lean_ctor_get_uint8(v___x_1955_, sizeof(void*)*11);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1969_ = v___x_1955_;
v_isShared_1970_ = v_isSharedCheck_1988_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_instanceOverrides_1966_);
lean_inc(v_canon_1956_);
lean_inc(v_issues_1965_);
lean_inc(v_extensions_1964_);
lean_inc(v_defEqI_1963_);
lean_inc(v_congrInfo_1962_);
lean_inc(v_getLevel_1961_);
lean_inc(v_inferType_1960_);
lean_inc(v_proofInstInfo_1959_);
lean_inc(v_maxFVar_1958_);
lean_inc(v_share_1957_);
lean_dec(v___x_1955_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1988_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_cache_1971_; lean_object* v_cacheInType_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1987_; 
v_cache_1971_ = lean_ctor_get(v_canon_1956_, 0);
v_cacheInType_1972_ = lean_ctor_get(v_canon_1956_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_canon_1956_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1974_ = v_canon_1956_;
v_isShared_1975_ = v_isSharedCheck_1987_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_cacheInType_1972_);
lean_inc(v_cache_1971_);
lean_dec(v_canon_1956_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1987_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_inc(v_a_1951_);
v___x_1976_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1972_, v_e_1906_, v_a_1951_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_cache_1971_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 9, v___x_1978_);
v___x_1980_ = v___x_1969_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_share_1957_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_maxFVar_1958_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_proofInstInfo_1959_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_inferType_1960_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_getLevel_1961_);
lean_ctor_set(v_reuseFailAlloc_1985_, 5, v_congrInfo_1962_);
lean_ctor_set(v_reuseFailAlloc_1985_, 6, v_defEqI_1963_);
lean_ctor_set(v_reuseFailAlloc_1985_, 7, v_extensions_1964_);
lean_ctor_set(v_reuseFailAlloc_1985_, 8, v_issues_1965_);
lean_ctor_set(v_reuseFailAlloc_1985_, 9, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1985_, 10, v_instanceOverrides_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*11, v_debug_1967_);
v___x_1980_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_st_ref_set(v_a_1909_, v___x_1980_);
if (v_isShared_1954_ == 0)
{
v___x_1983_ = v___x_1953_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1951_);
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
}
}
}
else
{
lean_dec_ref(v_e_1906_);
return v___y_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2044_, lean_object* v_a_2045_, lean_object* v___x_2046_, lean_object* v_snd_2047_, uint8_t v___x_2048_, lean_object* v_fst_2049_, lean_object* v_____r_2050_, uint8_t v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_arg_x27_2060_; lean_object* v___x_2072_; 
lean_inc_ref(v___x_2046_);
v___x_2072_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2044_, v_a_2045_, v___x_2046_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; uint8_t v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = lean_unbox(v_a_2073_);
lean_dec(v_a_2073_);
switch(v___x_2074_)
{
case 0:
{
lean_object* v___x_2075_; 
lean_inc_ref(v___x_2046_);
v___x_2075_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2046_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v_arg_x27_2060_ = v_a_2076_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2077_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
case 1:
{
lean_object* v___x_2085_; 
lean_inc_ref(v___x_2046_);
v___x_2085_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2046_, v___y_2055_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2105_ = l_Lean_Expr_cleanupAnnotations(v_a_2086_);
v___x_2106_ = l_Lean_Expr_isApp(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2105_);
v___y_2088_ = v___y_2051_;
v___y_2089_ = v___y_2052_;
v___y_2090_ = v___y_2053_;
v___y_2091_ = v___y_2054_;
v___y_2092_ = v___y_2055_;
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
goto v___jp_2087_;
}
else
{
lean_object* v_arg_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v_arg_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc_ref(v_arg_2107_);
v___x_2108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2105_);
v___x_2109_ = l_Lean_Expr_isApp(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
v___y_2088_ = v___y_2051_;
v___y_2089_ = v___y_2052_;
v___y_2090_ = v___y_2053_;
v___y_2091_ = v___y_2054_;
v___y_2092_ = v___y_2055_;
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
goto v___jp_2087_;
}
else
{
lean_object* v_arg_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_arg_2110_ = lean_ctor_get(v___x_2108_, 1);
lean_inc_ref(v_arg_2110_);
v___x_2111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2108_);
v___x_2112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2115_ = l_Lean_Expr_isConstOf(v___x_2111_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec_ref(v___x_2111_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
v___y_2088_ = v___y_2051_;
v___y_2089_ = v___y_2052_;
v___y_2090_ = v___y_2053_;
v___y_2091_ = v___y_2054_;
v___y_2092_ = v___y_2055_;
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2116_; 
lean_inc_ref(v___x_2046_);
v___x_2116_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2111_, v_arg_2110_, v_arg_2107_, v___x_2046_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_arg_x27_2060_ = v_a_2117_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2118_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2116_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
else
{
lean_object* v___x_2126_; 
lean_inc_ref(v___x_2046_);
v___x_2126_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2111_, v_arg_2110_, v_arg_2107_, v___x_2046_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_arg_x27_2060_ = v_a_2127_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
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
}
v___jp_2087_:
{
lean_object* v___x_2095_; 
lean_inc_ref(v___x_2046_);
v___x_2095_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2046_, v___x_2048_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_arg_x27_2060_ = v_a_2096_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2097_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2095_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2136_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2085_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2085_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
default: 
{
lean_object* v___x_2144_; 
lean_inc_ref(v___x_2046_);
v___x_2144_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2046_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_arg_x27_2060_ = v_a_2145_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2144_);
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
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_fst_2049_);
lean_dec(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v_a_2154_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2072_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2072_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
v___jp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = lean_ptr_addr(v___x_2046_);
lean_dec_ref(v___x_2046_);
v___x_2062_ = lean_ptr_addr(v_arg_x27_2060_);
v___x_2063_ = lean_usize_dec_eq(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_fst_2049_);
v___x_2064_ = lean_array_fset(v_snd_2047_, v_a_2045_, v_arg_x27_2060_);
v___x_2065_ = lean_box(v___x_2048_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2064_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec_ref(v_arg_x27_2060_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_fst_2049_);
lean_ctor_set(v___x_2069_, 1, v_snd_2047_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2166_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2167_ = l_Lean_Name_append(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2170_ = l_Lean_stringToMessageData(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2177_, lean_object* v___x_2178_, lean_object* v_a_2179_, lean_object* v_b_2180_, uint8_t v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___y_2190_; uint8_t v___x_2212_; 
v___x_2212_ = lean_nat_dec_lt(v_a_2179_, v_upperBound_2177_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec(v_a_2179_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_b_2180_);
return v___x_2213_;
}
else
{
lean_object* v_options_2214_; lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2280_; 
v_options_2214_ = lean_ctor_get(v___y_2186_, 2);
v_fst_2215_ = lean_ctor_get(v_b_2180_, 0);
v_snd_2216_ = lean_ctor_get(v_b_2180_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_b_2180_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2218_ = v_b_2180_;
v_isShared_2219_ = v_isSharedCheck_2280_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_snd_2216_);
lean_inc(v_fst_2215_);
lean_dec(v_b_2180_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2280_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_inheritedTraceOptions_2220_; uint8_t v_hasTrace_2221_; lean_object* v___x_2222_; 
v_inheritedTraceOptions_2220_ = lean_ctor_get(v___y_2186_, 13);
v_hasTrace_2221_ = lean_ctor_get_uint8(v_options_2214_, sizeof(void*)*1);
v___x_2222_ = lean_array_fget(v_snd_2216_, v_a_2179_);
if (v_hasTrace_2221_ == 0)
{
lean_del_object(v___x_2218_);
goto v___jp_2223_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2227_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2220_, v_options_2214_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_del_object(v___x_2218_);
goto v___jp_2223_;
}
else
{
lean_object* v___x_2229_; 
lean_inc(v___x_2222_);
v___x_2229_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2178_, v_a_2179_, v___x_2222_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v___y_2184_);
lean_inc(v___x_2222_);
v___x_2231_ = lean_infer_type(v___x_2222_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___y_2235_; uint8_t v___x_2259_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2259_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
switch(v___x_2259_)
{
case 0:
{
lean_object* v___x_2260_; 
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2235_ = v___x_2260_;
goto v___jp_2234_;
}
case 1:
{
lean_object* v___x_2261_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2235_ = v___x_2261_;
goto v___jp_2234_;
}
case 2:
{
lean_object* v___x_2262_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2235_ = v___x_2262_;
goto v___jp_2234_;
}
default: 
{
lean_object* v___x_2263_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2235_ = v___x_2263_;
goto v___jp_2234_;
}
}
v___jp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_inc(v___y_2235_);
v___x_2236_ = l_Lean_MessageData_ofFormat(v___y_2235_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 7);
lean_ctor_set(v___x_2218_, 1, v___x_2236_);
lean_ctor_set(v___x_2218_, 0, v___x_2233_);
v___x_2238_ = v___x_2218_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2239_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
lean_inc(v___x_2222_);
v___x_2241_ = l_Lean_MessageData_ofExpr(v___x_2222_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_MessageData_ofExpr(v_a_2232_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2226_, v___x_2246_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2249_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v___x_2249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2178_, v_a_2179_, v___x_2222_, v_snd_2216_, v___x_2212_, v_fst_2215_, v_a_2248_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2249_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v___x_2222_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
lean_dec(v_a_2179_);
v_a_2250_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2247_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2247_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2230_);
lean_dec(v___x_2222_);
lean_del_object(v___x_2218_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
lean_dec(v_a_2179_);
v_a_2264_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2231_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2231_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v___x_2222_);
lean_del_object(v___x_2218_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
lean_dec(v_a_2179_);
v_a_2272_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2229_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2229_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
v___jp_2223_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2178_, v_a_2179_, v___x_2222_, v_snd_2216_, v___x_2212_, v_fst_2215_, v___x_2224_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2225_;
goto v___jp_2189_;
}
}
}
v___jp_2189_:
{
if (lean_obj_tag(v___y_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2203_; 
v_a_2191_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2193_ = v___y_2190_;
v_isShared_2194_ = v_isSharedCheck_2203_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___y_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2203_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
if (lean_obj_tag(v_a_2191_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; 
lean_dec(v_a_2179_);
v_a_2195_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v_a_2191_, 1);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v_a_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_del_object(v___x_2193_);
v_a_2199_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v_a_2191_, 1);
v___x_2200_ = lean_unsigned_to_nat(1u);
v___x_2201_ = lean_nat_add(v_a_2179_, v___x_2200_);
lean_dec(v_a_2179_);
v_a_2179_ = v___x_2201_;
v_b_2180_ = v_a_2199_;
goto _start;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2179_);
v_a_2204_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___y_2190_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___y_2190_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_, uint8_t v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___y_2294_; uint8_t v_modified_2295_; lean_object* v_f_2296_; uint8_t v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v_args_2352_; uint8_t v_modified_2353_; uint8_t v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; 
if (lean_obj_tag(v_x_2282_) == 5)
{
lean_object* v_fn_2389_; lean_object* v_arg_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_fn_2389_ = lean_ctor_get(v_x_2282_, 0);
lean_inc_ref(v_fn_2389_);
v_arg_2390_ = lean_ctor_get(v_x_2282_, 1);
lean_inc_ref(v_arg_2390_);
lean_dec_ref_known(v_x_2282_, 2);
v___x_2391_ = lean_array_set(v_x_2283_, v_x_2284_, v_arg_2390_);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_sub(v_x_2284_, v___x_2392_);
lean_dec(v_x_2284_);
v_x_2282_ = v_fn_2389_;
v_x_2283_ = v___x_2391_;
v_x_2284_ = v___x_2393_;
goto _start;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
lean_dec(v_x_2284_);
v___x_2395_ = lean_array_get_size(v_x_2283_);
v___x_2396_ = lean_unsigned_to_nat(2u);
v___x_2397_ = lean_nat_dec_eq(v___x_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
v___y_2368_ = v___y_2285_;
v___y_2369_ = v___y_2286_;
v___y_2370_ = v___y_2287_;
v___y_2371_ = v___y_2288_;
v___y_2372_ = v___y_2289_;
v___y_2373_ = v___y_2290_;
v___y_2374_ = v___y_2291_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2399_ = l_Lean_Expr_isConstOf(v_x_2282_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2401_ = l_Lean_Expr_isConstOf(v_x_2282_, v___x_2400_);
if (v___x_2401_ == 0)
{
v___y_2368_ = v___y_2285_;
v___y_2369_ = v___y_2286_;
v___y_2370_ = v___y_2287_;
v___y_2371_ = v___y_2288_;
v___y_2372_ = v___y_2289_;
v___y_2373_ = v___y_2290_;
v___y_2374_ = v___y_2291_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2402_ = l_Lean_instInhabitedExpr;
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_array_get(v___x_2402_, v_x_2283_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_array_get(v___x_2402_, v_x_2283_, v___x_2405_);
lean_dec_ref(v_x_2283_);
v___x_2407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2282_, v___x_2404_, v___x_2406_, v_e_2281_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2407_;
}
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_prop_2410_; lean_object* v___x_2411_; 
v___x_2408_ = l_Lean_instInhabitedExpr;
v___x_2409_ = lean_unsigned_to_nat(0u);
v_prop_2410_ = lean_array_get_borrowed(v___x_2408_, v_x_2283_, v___x_2409_);
lean_inc(v_prop_2410_);
v___x_2411_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2410_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2428_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
size_t v___x_2416_; size_t v___x_2417_; uint8_t v___x_2418_; 
v___x_2416_ = lean_ptr_addr(v_prop_2410_);
v___x_2417_ = lean_ptr_addr(v_a_2412_);
v___x_2418_ = lean_usize_dec_eq(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec_ref(v_e_2281_);
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_array_get(v___x_2408_, v_x_2283_, v___x_2419_);
lean_dec_ref(v_x_2283_);
v___x_2421_ = l_Lean_mkAppB(v_x_2282_, v_a_2412_, v___x_2420_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2421_);
v___x_2423_ = v___x_2414_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
else
{
lean_object* v___x_2426_; 
lean_dec(v_a_2412_);
lean_dec_ref(v_x_2283_);
lean_dec_ref(v_x_2282_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v_e_2281_);
v___x_2426_ = v___x_2414_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_e_2281_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_dec_ref(v_x_2283_);
lean_dec_ref(v_x_2282_);
lean_dec_ref(v_e_2281_);
return v___x_2411_;
}
}
}
}
v___jp_2293_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_box(0);
lean_inc_ref(v_f_2296_);
v___x_2305_ = l_Lean_Meta_getFunInfo(v_f_2296_, v___x_2304_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_paramInfo_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2341_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_paramInfo_2307_ = lean_ctor_get(v_a_2306_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_a_2306_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v_a_2306_, 1);
lean_dec(v_unused_2342_);
v___x_2309_ = v_a_2306_;
v_isShared_2310_ = v_isSharedCheck_2341_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_paramInfo_2307_);
lean_dec(v_a_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2341_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2311_ = lean_array_get_size(v___y_2294_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_box(v_modified_2295_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___y_2294_);
lean_ctor_set(v___x_2309_, 0, v___x_2313_);
v___x_2315_ = v___x_2309_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___y_2294_);
v___x_2315_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2311_, v_paramInfo_2307_, v___x_2312_, v___x_2315_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec_ref(v_paramInfo_2307_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2331_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; uint8_t v___x_2322_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
v___x_2322_ = lean_unbox(v_fst_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2324_; 
lean_dec(v_a_2317_);
lean_dec_ref(v_f_2296_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_e_2281_);
v___x_2324_ = v___x_2319_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_e_2281_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
else
{
lean_object* v_snd_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_dec_ref(v_e_2281_);
v_snd_2326_ = lean_ctor_get(v_a_2317_, 1);
lean_inc(v_snd_2326_);
lean_dec(v_a_2317_);
v___x_2327_ = l_Lean_mkAppN(v_f_2296_, v_snd_2326_);
lean_dec(v_snd_2326_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2327_);
v___x_2329_ = v___x_2319_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
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
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_f_2296_);
lean_dec_ref(v_e_2281_);
v_a_2332_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2316_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2316_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_f_2296_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_e_2281_);
v_a_2343_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2305_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2305_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
v___jp_2351_:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_x_2282_);
v___x_2361_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2282_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; size_t v___x_2363_; size_t v___x_2364_; uint8_t v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_ptr_addr(v_x_2282_);
v___x_2364_ = lean_ptr_addr(v_a_2362_);
v___x_2365_ = lean_usize_dec_eq(v___x_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
uint8_t v___x_2366_; 
lean_dec_ref(v_x_2282_);
v___x_2366_ = 1;
v___y_2294_ = v_args_2352_;
v_modified_2295_ = v___x_2366_;
v_f_2296_ = v_a_2362_;
v___y_2297_ = v___y_2354_;
v___y_2298_ = v___y_2355_;
v___y_2299_ = v___y_2356_;
v___y_2300_ = v___y_2357_;
v___y_2301_ = v___y_2358_;
v___y_2302_ = v___y_2359_;
v___y_2303_ = v___y_2360_;
goto v___jp_2293_;
}
else
{
lean_dec(v_a_2362_);
v___y_2294_ = v_args_2352_;
v_modified_2295_ = v_modified_2353_;
v_f_2296_ = v_x_2282_;
v___y_2297_ = v___y_2354_;
v___y_2298_ = v___y_2355_;
v___y_2299_ = v___y_2356_;
v___y_2300_ = v___y_2357_;
v___y_2301_ = v___y_2358_;
v___y_2302_ = v___y_2359_;
v___y_2303_ = v___y_2360_;
goto v___jp_2293_;
}
}
else
{
lean_dec_ref(v_args_2352_);
lean_dec_ref(v_x_2282_);
lean_dec_ref(v_e_2281_);
return v___x_2361_;
}
}
v___jp_2367_:
{
uint8_t v_modified_2375_; lean_object* v___x_2376_; uint8_t v_modified_2377_; 
v_modified_2375_ = 0;
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2377_ = l_Lean_Expr_isConstOf(v_x_2282_, v___x_2376_);
if (v_modified_2377_ == 0)
{
v_args_2352_ = v_x_2283_;
v_modified_2353_ = v_modified_2375_;
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2369_;
v___y_2356_ = v___y_2370_;
v___y_2357_ = v___y_2371_;
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2378_; 
lean_inc_ref(v_x_2283_);
v___x_2378_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2283_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
if (lean_obj_tag(v_a_2379_) == 1)
{
lean_object* v_val_2380_; 
lean_dec_ref(v_x_2283_);
v_val_2380_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v_a_2379_, 1);
v_args_2352_ = v_val_2380_;
v_modified_2353_ = v_modified_2377_;
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2369_;
v___y_2356_ = v___y_2370_;
v___y_2357_ = v___y_2371_;
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
goto v___jp_2351_;
}
else
{
lean_dec(v_a_2379_);
v_args_2352_ = v_x_2283_;
v_modified_2353_ = v_modified_2375_;
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2369_;
v___y_2356_ = v___y_2370_;
v___y_2357_ = v___y_2371_;
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
goto v___jp_2351_;
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_x_2283_);
lean_dec_ref(v_x_2282_);
lean_dec_ref(v_e_2281_);
v_a_2381_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2378_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2378_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2429_, uint8_t v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_dummy_2438_; lean_object* v_nargs_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_dummy_2438_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2439_ = l_Lean_Expr_getAppNumArgs(v_e_2429_);
lean_inc(v_nargs_2439_);
v___x_2440_ = lean_mk_array(v_nargs_2439_, v_dummy_2438_);
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = lean_nat_sub(v_nargs_2439_, v___x_2441_);
lean_dec(v_nargs_2439_);
lean_inc_ref(v_e_2429_);
v___x_2443_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2429_, v_e_2429_, v___x_2440_, v___x_2442_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2444_, uint8_t v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2454_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
return v___x_2455_;
}
else
{
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2456_, uint8_t v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2456_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
if (lean_obj_tag(v_a_2466_) == 0)
{
lean_object* v_val_2467_; lean_object* v___x_2468_; 
lean_dec_ref(v_e_2456_);
v_val_2467_ = lean_ctor_get(v_a_2466_, 0);
lean_inc_ref(v_val_2467_);
lean_dec_ref_known(v_a_2466_, 1);
v___x_2468_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2467_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; 
lean_dec(v_a_2466_);
v___x_2469_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2470_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2481_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
if (lean_obj_tag(v_a_2472_) == 0)
{
lean_object* v_val_2476_; lean_object* v___x_2477_; 
lean_del_object(v___x_2474_);
lean_dec(v_a_2470_);
v_val_2476_ = lean_ctor_get(v_a_2472_, 0);
lean_inc_ref(v_val_2476_);
lean_dec_ref_known(v_a_2472_, 1);
v___x_2477_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2476_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
return v___x_2477_;
}
else
{
lean_object* v___x_2479_; 
lean_dec(v_a_2472_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v_a_2470_);
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2470_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_a_2470_);
v_a_2482_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2471_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2471_);
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
else
{
return v___x_2469_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec_ref(v_e_2456_);
v_a_2490_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2465_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2465_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2504_, uint8_t v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
lean_inc_ref(v_e_2504_);
v___x_2513_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2504_, v_a_2509_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2525_ = l_Lean_Expr_cleanupAnnotations(v_a_2514_);
v___x_2526_ = l_Lean_Expr_isApp(v___x_2525_);
if (v___x_2526_ == 0)
{
lean_dec_ref(v___x_2525_);
v___y_2516_ = v_a_2505_;
v___y_2517_ = v_a_2506_;
v___y_2518_ = v_a_2507_;
v___y_2519_ = v_a_2508_;
v___y_2520_ = v_a_2509_;
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
goto v___jp_2515_;
}
else
{
lean_object* v_arg_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_arg_2527_ = lean_ctor_get(v___x_2525_, 1);
lean_inc_ref(v_arg_2527_);
v___x_2528_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2525_);
v___x_2529_ = l_Lean_Expr_isApp(v___x_2528_);
if (v___x_2529_ == 0)
{
lean_dec_ref(v___x_2528_);
lean_dec_ref(v_arg_2527_);
v___y_2516_ = v_a_2505_;
v___y_2517_ = v_a_2506_;
v___y_2518_ = v_a_2507_;
v___y_2519_ = v_a_2508_;
v___y_2520_ = v_a_2509_;
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
goto v___jp_2515_;
}
else
{
lean_object* v_arg_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_arg_2530_ = lean_ctor_get(v___x_2528_, 1);
lean_inc_ref(v_arg_2530_);
v___x_2531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2528_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2533_ = l_Lean_Expr_isConstOf(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_dec_ref(v___x_2531_);
lean_dec_ref(v_arg_2530_);
lean_dec_ref(v_arg_2527_);
v___y_2516_ = v_a_2505_;
v___y_2517_ = v_a_2506_;
v___y_2518_ = v_a_2507_;
v___y_2519_ = v_a_2508_;
v___y_2520_ = v_a_2509_;
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2531_, v_arg_2530_, v_arg_2527_, v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2534_;
}
}
}
v___jp_2515_:
{
uint8_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = 0;
v___x_2524_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2504_, v___x_2523_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2524_;
}
}
else
{
lean_dec_ref(v_e_2504_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2535_, lean_object* v_00_u03b1_2536_, lean_object* v_c_2537_, lean_object* v_inst_2538_, lean_object* v_a_2539_, lean_object* v_b_2540_, uint8_t v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2537_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; uint8_t v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc_n(v_a_2550_, 2);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2550_);
if (v___x_2551_ == 0)
{
uint8_t v___x_2552_; 
lean_inc(v_a_2550_);
v___x_2552_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2550_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2536_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2538_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2539_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2559_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2568_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_mkApp5(v_f_2535_, v_a_2554_, v_a_2550_, v_a_2556_, v_a_2558_, v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
lean_dec(v_a_2558_);
lean_dec(v_a_2556_);
lean_dec(v_a_2554_);
lean_dec(v_a_2550_);
lean_dec_ref(v_f_2535_);
return v___x_2559_;
}
}
else
{
lean_dec(v_a_2556_);
lean_dec(v_a_2554_);
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_f_2535_);
return v___x_2557_;
}
}
else
{
lean_dec(v_a_2554_);
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_f_2535_);
return v___x_2555_;
}
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_f_2535_);
return v___x_2553_;
}
}
else
{
lean_object* v___x_2569_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
v___x_2569_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2569_;
}
}
else
{
lean_object* v___x_2570_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
v___x_2570_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2539_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2570_;
}
}
else
{
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2571_, lean_object* v_00_u03b1_2572_, lean_object* v_c_2573_, lean_object* v_a_2574_, lean_object* v_b_2575_, uint8_t v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2573_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_n(v_a_2585_, 2);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = l_Lean_Expr_isBoolTrue(v_a_2585_);
if (v___x_2586_ == 0)
{
uint8_t v___x_2587_; 
lean_inc(v_a_2585_);
v___x_2587_ = l_Lean_Expr_isBoolFalse(v_a_2585_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2572_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2574_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2601_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = l_Lean_mkApp4(v_f_2571_, v_a_2589_, v_a_2585_, v_a_2591_, v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_dec(v_a_2591_);
lean_dec(v_a_2589_);
lean_dec(v_a_2585_);
lean_dec_ref(v_f_2571_);
return v___x_2592_;
}
}
else
{
lean_dec(v_a_2589_);
lean_dec(v_a_2585_);
lean_dec_ref(v_b_2575_);
lean_dec_ref(v_f_2571_);
return v___x_2590_;
}
}
else
{
lean_dec(v_a_2585_);
lean_dec_ref(v_b_2575_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_f_2571_);
return v___x_2588_;
}
}
else
{
lean_object* v___x_2602_; 
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_00_u03b1_2572_);
lean_dec_ref(v_f_2571_);
v___x_2602_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
return v___x_2602_;
}
}
else
{
lean_object* v___x_2603_; 
lean_dec(v_a_2585_);
lean_dec_ref(v_b_2575_);
lean_dec_ref(v_00_u03b1_2572_);
lean_dec_ref(v_f_2571_);
v___x_2603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2574_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
return v___x_2603_;
}
}
else
{
lean_dec_ref(v_b_2575_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_00_u03b1_2572_);
lean_dec_ref(v_f_2571_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2604_, uint8_t v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v___x_2613_; 
lean_inc_ref(v_e_2604_);
v___x_2613_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2604_, v_a_2609_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; uint8_t v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2639_ = l_Lean_Expr_cleanupAnnotations(v_a_2614_);
v___x_2640_ = l_Lean_Expr_isApp(v___x_2639_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v___x_2639_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v_arg_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_arg_2641_ = lean_ctor_get(v___x_2639_, 1);
lean_inc_ref(v_arg_2641_);
v___x_2642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2639_);
v___x_2643_ = l_Lean_Expr_isApp(v___x_2642_);
if (v___x_2643_ == 0)
{
lean_dec_ref(v___x_2642_);
lean_dec_ref(v_arg_2641_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v_arg_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_arg_2644_ = lean_ctor_get(v___x_2642_, 1);
lean_inc_ref(v_arg_2644_);
v___x_2645_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2642_);
v___x_2646_ = l_Lean_Expr_isApp(v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v___x_2645_);
lean_dec_ref(v_arg_2644_);
lean_dec_ref(v_arg_2641_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v_arg_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_arg_2647_ = lean_ctor_get(v___x_2645_, 1);
lean_inc_ref(v_arg_2647_);
v___x_2648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2645_);
v___x_2649_ = l_Lean_Expr_isApp(v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_arg_2644_);
lean_dec_ref(v_arg_2641_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v_arg_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v_arg_2650_ = lean_ctor_get(v___x_2648_, 1);
lean_inc_ref(v_arg_2650_);
v___x_2651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2648_);
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2653_ = l_Lean_Expr_isConstOf(v___x_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_Expr_isApp(v___x_2651_);
if (v___x_2654_ == 0)
{
lean_dec_ref(v___x_2651_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_arg_2644_);
lean_dec_ref(v_arg_2641_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v_arg_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_arg_2655_ = lean_ctor_get(v___x_2651_, 1);
lean_inc_ref(v_arg_2655_);
v___x_2656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2651_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2658_ = l_Lean_Expr_isConstOf(v___x_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_arg_2655_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_arg_2644_);
lean_dec_ref(v_arg_2641_);
v___y_2616_ = v_a_2605_;
v___y_2617_ = v_a_2606_;
v___y_2618_ = v_a_2607_;
v___y_2619_ = v_a_2608_;
v___y_2620_ = v_a_2609_;
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v_e_2604_);
v___x_2659_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2656_, v_arg_2655_, v_arg_2650_, v_arg_2647_, v_arg_2644_, v_arg_2641_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
return v___x_2659_;
}
}
}
else
{
lean_object* v___x_2660_; 
lean_dec_ref(v_e_2604_);
v___x_2660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2651_, v_arg_2650_, v_arg_2647_, v_arg_2644_, v_arg_2641_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
return v___x_2660_;
}
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Expr_getAppFn(v_e_2604_);
if (lean_obj_tag(v___x_2623_) == 4)
{
lean_object* v_declName_2624_; lean_object* v___x_2625_; 
v_declName_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_declName_2624_);
lean_dec_ref_known(v___x_2623_, 2);
v___x_2625_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2624_, v___y_2622_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; uint8_t v___x_2627_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = lean_unbox(v_a_2626_);
lean_dec(v_a_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2604_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2604_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2629_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_e_2604_);
v_a_2630_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2625_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2625_);
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
else
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2623_);
v___x_2638_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2604_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2638_;
}
}
}
else
{
lean_dec_ref(v_e_2604_);
return v___x_2613_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2664_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2665_ = lean_unsigned_to_nat(18u);
v___x_2666_ = lean_unsigned_to_nat(1896u);
v___x_2667_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2668_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2669_ = l_mkPanicMessageWithDecl(v___x_2668_, v___x_2667_, v___x_2666_, v___x_2665_, v___x_2664_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2670_, uint8_t v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = l_Lean_Expr_projExpr_x21(v_e_2670_);
v___x_2680_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2679_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___y_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
if (lean_obj_tag(v_e_2670_) == 11)
{
lean_object* v_typeName_2705_; lean_object* v_idx_2706_; lean_object* v_struct_2707_; size_t v___x_2708_; size_t v___x_2709_; uint8_t v___x_2710_; 
v_typeName_2705_ = lean_ctor_get(v_e_2670_, 0);
v_idx_2706_ = lean_ctor_get(v_e_2670_, 1);
v_struct_2707_ = lean_ctor_get(v_e_2670_, 2);
v___x_2708_ = lean_ptr_addr(v_struct_2707_);
v___x_2709_ = lean_ptr_addr(v_a_2681_);
v___x_2710_ = lean_usize_dec_eq(v___x_2708_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_inc(v_idx_2706_);
lean_inc(v_typeName_2705_);
lean_dec_ref_known(v_e_2670_, 3);
v___x_2711_ = l_Lean_Expr_proj___override(v_typeName_2705_, v_idx_2706_, v_a_2681_);
v___y_2683_ = v___x_2711_;
goto v___jp_2682_;
}
else
{
lean_dec(v_a_2681_);
v___y_2683_ = v_e_2670_;
goto v___jp_2682_;
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v_a_2681_);
lean_dec_ref(v_e_2670_);
v___x_2712_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2713_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2712_);
v___y_2683_ = v___x_2713_;
goto v___jp_2682_;
}
v___jp_2682_:
{
lean_object* v___x_2684_; 
lean_inc_ref(v___y_2683_);
v___x_2684_ = l_Lean_Meta_reduceProj_x3f(v___y_2683_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2696_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
if (lean_obj_tag(v_a_2685_) == 0)
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___y_2683_);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___y_2683_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
lean_object* v_val_2692_; lean_object* v___x_2694_; 
lean_dec_ref(v___y_2683_);
v_val_2692_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_val_2692_);
lean_dec_ref_known(v_a_2685_, 1);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v_val_2692_);
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_val_2692_);
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
lean_dec_ref(v___y_2683_);
v_a_2697_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2684_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2684_);
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
else
{
lean_dec_ref(v_e_2670_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2714_, uint8_t v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
switch(lean_obj_tag(v_e_2714_))
{
case 7:
{
lean_object* v___x_2723_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2715_ == 0)
{
lean_object* v___x_2724_; lean_object* v_canon_2725_; lean_object* v_cache_2726_; lean_object* v___x_2727_; 
v___x_2724_ = lean_st_ref_get(v_a_2717_);
v_canon_2725_ = lean_ctor_get(v___x_2724_, 9);
lean_inc_ref(v_canon_2725_);
lean_dec(v___x_2724_);
v_cache_2726_ = lean_ctor_get(v_canon_2725_, 0);
lean_inc_ref(v_cache_2726_);
lean_dec_ref(v_canon_2725_);
v___x_2727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2726_, v_e_2714_);
lean_dec_ref(v_cache_2726_);
if (lean_obj_tag(v___x_2727_) == 1)
{
lean_object* v_val_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_val_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 0);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_val_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec(v___x_2727_);
lean_inc_ref(v_e_2714_);
v___x_2736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2723_, v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2775_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2775_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2775_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v_canon_2742_; lean_object* v_share_2743_; lean_object* v_maxFVar_2744_; lean_object* v_proofInstInfo_2745_; lean_object* v_inferType_2746_; lean_object* v_getLevel_2747_; lean_object* v_congrInfo_2748_; lean_object* v_defEqI_2749_; lean_object* v_extensions_2750_; lean_object* v_issues_2751_; lean_object* v_instanceOverrides_2752_; uint8_t v_debug_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2774_; 
v___x_2741_ = lean_st_ref_take(v_a_2717_);
v_canon_2742_ = lean_ctor_get(v___x_2741_, 9);
v_share_2743_ = lean_ctor_get(v___x_2741_, 0);
v_maxFVar_2744_ = lean_ctor_get(v___x_2741_, 1);
v_proofInstInfo_2745_ = lean_ctor_get(v___x_2741_, 2);
v_inferType_2746_ = lean_ctor_get(v___x_2741_, 3);
v_getLevel_2747_ = lean_ctor_get(v___x_2741_, 4);
v_congrInfo_2748_ = lean_ctor_get(v___x_2741_, 5);
v_defEqI_2749_ = lean_ctor_get(v___x_2741_, 6);
v_extensions_2750_ = lean_ctor_get(v___x_2741_, 7);
v_issues_2751_ = lean_ctor_get(v___x_2741_, 8);
v_instanceOverrides_2752_ = lean_ctor_get(v___x_2741_, 10);
v_debug_2753_ = lean_ctor_get_uint8(v___x_2741_, sizeof(void*)*11);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2755_ = v___x_2741_;
v_isShared_2756_ = v_isSharedCheck_2774_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_instanceOverrides_2752_);
lean_inc(v_canon_2742_);
lean_inc(v_issues_2751_);
lean_inc(v_extensions_2750_);
lean_inc(v_defEqI_2749_);
lean_inc(v_congrInfo_2748_);
lean_inc(v_getLevel_2747_);
lean_inc(v_inferType_2746_);
lean_inc(v_proofInstInfo_2745_);
lean_inc(v_maxFVar_2744_);
lean_inc(v_share_2743_);
lean_dec(v___x_2741_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2774_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_cache_2757_; lean_object* v_cacheInType_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2773_; 
v_cache_2757_ = lean_ctor_get(v_canon_2742_, 0);
v_cacheInType_2758_ = lean_ctor_get(v_canon_2742_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_canon_2742_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2760_ = v_canon_2742_;
v_isShared_2761_ = v_isSharedCheck_2773_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_cacheInType_2758_);
lean_inc(v_cache_2757_);
lean_dec(v_canon_2742_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2773_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_inc(v_a_2737_);
v___x_2762_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2757_, v_e_2714_, v_a_2737_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2762_);
v___x_2764_ = v___x_2760_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_cacheInType_2758_);
v___x_2764_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2766_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 9, v___x_2764_);
v___x_2766_ = v___x_2755_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_share_2743_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_maxFVar_2744_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v_proofInstInfo_2745_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v_inferType_2746_);
lean_ctor_set(v_reuseFailAlloc_2771_, 4, v_getLevel_2747_);
lean_ctor_set(v_reuseFailAlloc_2771_, 5, v_congrInfo_2748_);
lean_ctor_set(v_reuseFailAlloc_2771_, 6, v_defEqI_2749_);
lean_ctor_set(v_reuseFailAlloc_2771_, 7, v_extensions_2750_);
lean_ctor_set(v_reuseFailAlloc_2771_, 8, v_issues_2751_);
lean_ctor_set(v_reuseFailAlloc_2771_, 9, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2771_, 10, v_instanceOverrides_2752_);
lean_ctor_set_uint8(v_reuseFailAlloc_2771_, sizeof(void*)*11, v_debug_2753_);
v___x_2766_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2767_ = lean_st_ref_set(v_a_2717_, v___x_2766_);
if (v_isShared_2740_ == 0)
{
v___x_2769_ = v___x_2739_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2737_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_2736_;
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v_canon_2777_; lean_object* v_cacheInType_2778_; lean_object* v___x_2779_; 
v___x_2776_ = lean_st_ref_get(v_a_2717_);
v_canon_2777_ = lean_ctor_get(v___x_2776_, 9);
lean_inc_ref(v_canon_2777_);
lean_dec(v___x_2776_);
v_cacheInType_2778_ = lean_ctor_get(v_canon_2777_, 1);
lean_inc_ref(v_cacheInType_2778_);
lean_dec_ref(v_canon_2777_);
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2778_, v_e_2714_);
lean_dec_ref(v_cacheInType_2778_);
if (lean_obj_tag(v___x_2779_) == 1)
{
lean_object* v_val_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_val_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_val_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
lean_object* v___x_2788_; 
lean_dec(v___x_2779_);
lean_inc_ref(v_e_2714_);
v___x_2788_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2723_, v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2827_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2827_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2827_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v_canon_2794_; lean_object* v_share_2795_; lean_object* v_maxFVar_2796_; lean_object* v_proofInstInfo_2797_; lean_object* v_inferType_2798_; lean_object* v_getLevel_2799_; lean_object* v_congrInfo_2800_; lean_object* v_defEqI_2801_; lean_object* v_extensions_2802_; lean_object* v_issues_2803_; lean_object* v_instanceOverrides_2804_; uint8_t v_debug_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2826_; 
v___x_2793_ = lean_st_ref_take(v_a_2717_);
v_canon_2794_ = lean_ctor_get(v___x_2793_, 9);
v_share_2795_ = lean_ctor_get(v___x_2793_, 0);
v_maxFVar_2796_ = lean_ctor_get(v___x_2793_, 1);
v_proofInstInfo_2797_ = lean_ctor_get(v___x_2793_, 2);
v_inferType_2798_ = lean_ctor_get(v___x_2793_, 3);
v_getLevel_2799_ = lean_ctor_get(v___x_2793_, 4);
v_congrInfo_2800_ = lean_ctor_get(v___x_2793_, 5);
v_defEqI_2801_ = lean_ctor_get(v___x_2793_, 6);
v_extensions_2802_ = lean_ctor_get(v___x_2793_, 7);
v_issues_2803_ = lean_ctor_get(v___x_2793_, 8);
v_instanceOverrides_2804_ = lean_ctor_get(v___x_2793_, 10);
v_debug_2805_ = lean_ctor_get_uint8(v___x_2793_, sizeof(void*)*11);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2807_ = v___x_2793_;
v_isShared_2808_ = v_isSharedCheck_2826_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_instanceOverrides_2804_);
lean_inc(v_canon_2794_);
lean_inc(v_issues_2803_);
lean_inc(v_extensions_2802_);
lean_inc(v_defEqI_2801_);
lean_inc(v_congrInfo_2800_);
lean_inc(v_getLevel_2799_);
lean_inc(v_inferType_2798_);
lean_inc(v_proofInstInfo_2797_);
lean_inc(v_maxFVar_2796_);
lean_inc(v_share_2795_);
lean_dec(v___x_2793_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2826_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_cache_2809_; lean_object* v_cacheInType_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2825_; 
v_cache_2809_ = lean_ctor_get(v_canon_2794_, 0);
v_cacheInType_2810_ = lean_ctor_get(v_canon_2794_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_canon_2794_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2812_ = v_canon_2794_;
v_isShared_2813_ = v_isSharedCheck_2825_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_cacheInType_2810_);
lean_inc(v_cache_2809_);
lean_dec(v_canon_2794_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2825_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
lean_inc(v_a_2789_);
v___x_2814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2810_, v_e_2714_, v_a_2789_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 1, v___x_2814_);
v___x_2816_ = v___x_2812_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_cache_2809_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2818_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 9, v___x_2816_);
v___x_2818_ = v___x_2807_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_share_2795_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_maxFVar_2796_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_proofInstInfo_2797_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_inferType_2798_);
lean_ctor_set(v_reuseFailAlloc_2823_, 4, v_getLevel_2799_);
lean_ctor_set(v_reuseFailAlloc_2823_, 5, v_congrInfo_2800_);
lean_ctor_set(v_reuseFailAlloc_2823_, 6, v_defEqI_2801_);
lean_ctor_set(v_reuseFailAlloc_2823_, 7, v_extensions_2802_);
lean_ctor_set(v_reuseFailAlloc_2823_, 8, v_issues_2803_);
lean_ctor_set(v_reuseFailAlloc_2823_, 9, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2823_, 10, v_instanceOverrides_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2823_, sizeof(void*)*11, v_debug_2805_);
v___x_2818_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_st_ref_set(v_a_2717_, v___x_2818_);
if (v_isShared_2792_ == 0)
{
v___x_2821_ = v___x_2791_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2789_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_2788_;
}
}
}
}
case 6:
{
if (v_a_2715_ == 0)
{
lean_object* v___x_2828_; lean_object* v_canon_2829_; lean_object* v_cache_2830_; lean_object* v___x_2831_; 
v___x_2828_ = lean_st_ref_get(v_a_2717_);
v_canon_2829_ = lean_ctor_get(v___x_2828_, 9);
lean_inc_ref(v_canon_2829_);
lean_dec(v___x_2828_);
v_cache_2830_ = lean_ctor_get(v_canon_2829_, 0);
lean_inc_ref(v_cache_2830_);
lean_dec_ref(v_canon_2829_);
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2830_, v_e_2714_);
lean_dec_ref(v_cache_2830_);
if (lean_obj_tag(v___x_2831_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 0);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_val_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
else
{
lean_object* v___x_2840_; 
lean_dec(v___x_2831_);
lean_inc_ref(v_e_2714_);
v___x_2840_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2879_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2879_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2879_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v_canon_2846_; lean_object* v_share_2847_; lean_object* v_maxFVar_2848_; lean_object* v_proofInstInfo_2849_; lean_object* v_inferType_2850_; lean_object* v_getLevel_2851_; lean_object* v_congrInfo_2852_; lean_object* v_defEqI_2853_; lean_object* v_extensions_2854_; lean_object* v_issues_2855_; lean_object* v_instanceOverrides_2856_; uint8_t v_debug_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2878_; 
v___x_2845_ = lean_st_ref_take(v_a_2717_);
v_canon_2846_ = lean_ctor_get(v___x_2845_, 9);
v_share_2847_ = lean_ctor_get(v___x_2845_, 0);
v_maxFVar_2848_ = lean_ctor_get(v___x_2845_, 1);
v_proofInstInfo_2849_ = lean_ctor_get(v___x_2845_, 2);
v_inferType_2850_ = lean_ctor_get(v___x_2845_, 3);
v_getLevel_2851_ = lean_ctor_get(v___x_2845_, 4);
v_congrInfo_2852_ = lean_ctor_get(v___x_2845_, 5);
v_defEqI_2853_ = lean_ctor_get(v___x_2845_, 6);
v_extensions_2854_ = lean_ctor_get(v___x_2845_, 7);
v_issues_2855_ = lean_ctor_get(v___x_2845_, 8);
v_instanceOverrides_2856_ = lean_ctor_get(v___x_2845_, 10);
v_debug_2857_ = lean_ctor_get_uint8(v___x_2845_, sizeof(void*)*11);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2859_ = v___x_2845_;
v_isShared_2860_ = v_isSharedCheck_2878_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_instanceOverrides_2856_);
lean_inc(v_canon_2846_);
lean_inc(v_issues_2855_);
lean_inc(v_extensions_2854_);
lean_inc(v_defEqI_2853_);
lean_inc(v_congrInfo_2852_);
lean_inc(v_getLevel_2851_);
lean_inc(v_inferType_2850_);
lean_inc(v_proofInstInfo_2849_);
lean_inc(v_maxFVar_2848_);
lean_inc(v_share_2847_);
lean_dec(v___x_2845_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2878_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_cache_2861_; lean_object* v_cacheInType_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2877_; 
v_cache_2861_ = lean_ctor_get(v_canon_2846_, 0);
v_cacheInType_2862_ = lean_ctor_get(v_canon_2846_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_canon_2846_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2864_ = v_canon_2846_;
v_isShared_2865_ = v_isSharedCheck_2877_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_cacheInType_2862_);
lean_inc(v_cache_2861_);
lean_dec(v_canon_2846_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2877_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_inc(v_a_2841_);
v___x_2866_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2861_, v_e_2714_, v_a_2841_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2866_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_cacheInType_2862_);
v___x_2868_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 9, v___x_2868_);
v___x_2870_ = v___x_2859_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_share_2847_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_maxFVar_2848_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_proofInstInfo_2849_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v_inferType_2850_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v_getLevel_2851_);
lean_ctor_set(v_reuseFailAlloc_2875_, 5, v_congrInfo_2852_);
lean_ctor_set(v_reuseFailAlloc_2875_, 6, v_defEqI_2853_);
lean_ctor_set(v_reuseFailAlloc_2875_, 7, v_extensions_2854_);
lean_ctor_set(v_reuseFailAlloc_2875_, 8, v_issues_2855_);
lean_ctor_set(v_reuseFailAlloc_2875_, 9, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 10, v_instanceOverrides_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2875_, sizeof(void*)*11, v_debug_2857_);
v___x_2870_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = lean_st_ref_set(v_a_2717_, v___x_2870_);
if (v_isShared_2844_ == 0)
{
v___x_2873_ = v___x_2843_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2841_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_2840_;
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v_canon_2881_; lean_object* v_cacheInType_2882_; lean_object* v___x_2883_; 
v___x_2880_ = lean_st_ref_get(v_a_2717_);
v_canon_2881_ = lean_ctor_get(v___x_2880_, 9);
lean_inc_ref(v_canon_2881_);
lean_dec(v___x_2880_);
v_cacheInType_2882_ = lean_ctor_get(v_canon_2881_, 1);
lean_inc_ref(v_cacheInType_2882_);
lean_dec_ref(v_canon_2881_);
v___x_2883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2882_, v_e_2714_);
lean_dec_ref(v_cacheInType_2882_);
if (lean_obj_tag(v___x_2883_) == 1)
{
lean_object* v_val_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_val_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 0);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_val_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v___x_2892_; 
lean_dec(v___x_2883_);
lean_inc_ref(v_e_2714_);
v___x_2892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2931_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2931_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2931_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v_canon_2898_; lean_object* v_share_2899_; lean_object* v_maxFVar_2900_; lean_object* v_proofInstInfo_2901_; lean_object* v_inferType_2902_; lean_object* v_getLevel_2903_; lean_object* v_congrInfo_2904_; lean_object* v_defEqI_2905_; lean_object* v_extensions_2906_; lean_object* v_issues_2907_; lean_object* v_instanceOverrides_2908_; uint8_t v_debug_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2930_; 
v___x_2897_ = lean_st_ref_take(v_a_2717_);
v_canon_2898_ = lean_ctor_get(v___x_2897_, 9);
v_share_2899_ = lean_ctor_get(v___x_2897_, 0);
v_maxFVar_2900_ = lean_ctor_get(v___x_2897_, 1);
v_proofInstInfo_2901_ = lean_ctor_get(v___x_2897_, 2);
v_inferType_2902_ = lean_ctor_get(v___x_2897_, 3);
v_getLevel_2903_ = lean_ctor_get(v___x_2897_, 4);
v_congrInfo_2904_ = lean_ctor_get(v___x_2897_, 5);
v_defEqI_2905_ = lean_ctor_get(v___x_2897_, 6);
v_extensions_2906_ = lean_ctor_get(v___x_2897_, 7);
v_issues_2907_ = lean_ctor_get(v___x_2897_, 8);
v_instanceOverrides_2908_ = lean_ctor_get(v___x_2897_, 10);
v_debug_2909_ = lean_ctor_get_uint8(v___x_2897_, sizeof(void*)*11);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2911_ = v___x_2897_;
v_isShared_2912_ = v_isSharedCheck_2930_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_instanceOverrides_2908_);
lean_inc(v_canon_2898_);
lean_inc(v_issues_2907_);
lean_inc(v_extensions_2906_);
lean_inc(v_defEqI_2905_);
lean_inc(v_congrInfo_2904_);
lean_inc(v_getLevel_2903_);
lean_inc(v_inferType_2902_);
lean_inc(v_proofInstInfo_2901_);
lean_inc(v_maxFVar_2900_);
lean_inc(v_share_2899_);
lean_dec(v___x_2897_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2930_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_cache_2913_; lean_object* v_cacheInType_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2929_; 
v_cache_2913_ = lean_ctor_get(v_canon_2898_, 0);
v_cacheInType_2914_ = lean_ctor_get(v_canon_2898_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_canon_2898_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2916_ = v_canon_2898_;
v_isShared_2917_ = v_isSharedCheck_2929_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_cacheInType_2914_);
lean_inc(v_cache_2913_);
lean_dec(v_canon_2898_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2929_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
lean_inc(v_a_2893_);
v___x_2918_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2914_, v_e_2714_, v_a_2893_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_cache_2913_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 9, v___x_2920_);
v___x_2922_ = v___x_2911_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_share_2899_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_maxFVar_2900_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_proofInstInfo_2901_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_inferType_2902_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_getLevel_2903_);
lean_ctor_set(v_reuseFailAlloc_2927_, 5, v_congrInfo_2904_);
lean_ctor_set(v_reuseFailAlloc_2927_, 6, v_defEqI_2905_);
lean_ctor_set(v_reuseFailAlloc_2927_, 7, v_extensions_2906_);
lean_ctor_set(v_reuseFailAlloc_2927_, 8, v_issues_2907_);
lean_ctor_set(v_reuseFailAlloc_2927_, 9, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2927_, 10, v_instanceOverrides_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*11, v_debug_2909_);
v___x_2922_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = lean_st_ref_set(v_a_2717_, v___x_2922_);
if (v_isShared_2896_ == 0)
{
v___x_2925_ = v___x_2895_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2893_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_2892_;
}
}
}
}
case 8:
{
lean_object* v___x_2932_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2715_ == 0)
{
lean_object* v___x_2933_; lean_object* v_canon_2934_; lean_object* v_cache_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_st_ref_get(v_a_2717_);
v_canon_2934_ = lean_ctor_get(v___x_2933_, 9);
lean_inc_ref(v_canon_2934_);
lean_dec(v___x_2933_);
v_cache_2935_ = lean_ctor_get(v_canon_2934_, 0);
lean_inc_ref(v_cache_2935_);
lean_dec_ref(v_canon_2934_);
v___x_2936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2935_, v_e_2714_);
lean_dec_ref(v_cache_2935_);
if (lean_obj_tag(v___x_2936_) == 1)
{
lean_object* v_val_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref_known(v_e_2714_, 4);
v_val_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_val_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 0);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_val_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v___x_2945_; 
lean_dec(v___x_2936_);
lean_inc_ref(v_e_2714_);
v___x_2945_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2932_, v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2984_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2984_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2984_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v_canon_2951_; lean_object* v_share_2952_; lean_object* v_maxFVar_2953_; lean_object* v_proofInstInfo_2954_; lean_object* v_inferType_2955_; lean_object* v_getLevel_2956_; lean_object* v_congrInfo_2957_; lean_object* v_defEqI_2958_; lean_object* v_extensions_2959_; lean_object* v_issues_2960_; lean_object* v_instanceOverrides_2961_; uint8_t v_debug_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2983_; 
v___x_2950_ = lean_st_ref_take(v_a_2717_);
v_canon_2951_ = lean_ctor_get(v___x_2950_, 9);
v_share_2952_ = lean_ctor_get(v___x_2950_, 0);
v_maxFVar_2953_ = lean_ctor_get(v___x_2950_, 1);
v_proofInstInfo_2954_ = lean_ctor_get(v___x_2950_, 2);
v_inferType_2955_ = lean_ctor_get(v___x_2950_, 3);
v_getLevel_2956_ = lean_ctor_get(v___x_2950_, 4);
v_congrInfo_2957_ = lean_ctor_get(v___x_2950_, 5);
v_defEqI_2958_ = lean_ctor_get(v___x_2950_, 6);
v_extensions_2959_ = lean_ctor_get(v___x_2950_, 7);
v_issues_2960_ = lean_ctor_get(v___x_2950_, 8);
v_instanceOverrides_2961_ = lean_ctor_get(v___x_2950_, 10);
v_debug_2962_ = lean_ctor_get_uint8(v___x_2950_, sizeof(void*)*11);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2964_ = v___x_2950_;
v_isShared_2965_ = v_isSharedCheck_2983_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_instanceOverrides_2961_);
lean_inc(v_canon_2951_);
lean_inc(v_issues_2960_);
lean_inc(v_extensions_2959_);
lean_inc(v_defEqI_2958_);
lean_inc(v_congrInfo_2957_);
lean_inc(v_getLevel_2956_);
lean_inc(v_inferType_2955_);
lean_inc(v_proofInstInfo_2954_);
lean_inc(v_maxFVar_2953_);
lean_inc(v_share_2952_);
lean_dec(v___x_2950_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2983_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_cache_2966_; lean_object* v_cacheInType_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2982_; 
v_cache_2966_ = lean_ctor_get(v_canon_2951_, 0);
v_cacheInType_2967_ = lean_ctor_get(v_canon_2951_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_canon_2951_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2969_ = v_canon_2951_;
v_isShared_2970_ = v_isSharedCheck_2982_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_cacheInType_2967_);
lean_inc(v_cache_2966_);
lean_dec(v_canon_2951_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2982_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_inc(v_a_2946_);
v___x_2971_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2966_, v_e_2714_, v_a_2946_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_cacheInType_2967_);
v___x_2973_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 9, v___x_2973_);
v___x_2975_ = v___x_2964_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_share_2952_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_maxFVar_2953_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_proofInstInfo_2954_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_inferType_2955_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_getLevel_2956_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_congrInfo_2957_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_defEqI_2958_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_extensions_2959_);
lean_ctor_set(v_reuseFailAlloc_2980_, 8, v_issues_2960_);
lean_ctor_set(v_reuseFailAlloc_2980_, 9, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2980_, 10, v_instanceOverrides_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*11, v_debug_2962_);
v___x_2975_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_st_ref_set(v_a_2717_, v___x_2975_);
if (v_isShared_2949_ == 0)
{
v___x_2978_ = v___x_2948_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2946_);
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
}
}
else
{
lean_dec_ref_known(v_e_2714_, 4);
return v___x_2945_;
}
}
}
else
{
lean_object* v___x_2985_; lean_object* v_canon_2986_; lean_object* v_cacheInType_2987_; lean_object* v___x_2988_; 
v___x_2985_ = lean_st_ref_get(v_a_2717_);
v_canon_2986_ = lean_ctor_get(v___x_2985_, 9);
lean_inc_ref(v_canon_2986_);
lean_dec(v___x_2985_);
v_cacheInType_2987_ = lean_ctor_get(v_canon_2986_, 1);
lean_inc_ref(v_cacheInType_2987_);
lean_dec_ref(v_canon_2986_);
v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2987_, v_e_2714_);
lean_dec_ref(v_cacheInType_2987_);
if (lean_obj_tag(v___x_2988_) == 1)
{
lean_object* v_val_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref_known(v_e_2714_, 4);
v_val_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_val_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 0);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_val_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v___x_2997_; 
lean_dec(v___x_2988_);
lean_inc_ref(v_e_2714_);
v___x_2997_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2932_, v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3036_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3036_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3036_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v_canon_3003_; lean_object* v_share_3004_; lean_object* v_maxFVar_3005_; lean_object* v_proofInstInfo_3006_; lean_object* v_inferType_3007_; lean_object* v_getLevel_3008_; lean_object* v_congrInfo_3009_; lean_object* v_defEqI_3010_; lean_object* v_extensions_3011_; lean_object* v_issues_3012_; lean_object* v_instanceOverrides_3013_; uint8_t v_debug_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3035_; 
v___x_3002_ = lean_st_ref_take(v_a_2717_);
v_canon_3003_ = lean_ctor_get(v___x_3002_, 9);
v_share_3004_ = lean_ctor_get(v___x_3002_, 0);
v_maxFVar_3005_ = lean_ctor_get(v___x_3002_, 1);
v_proofInstInfo_3006_ = lean_ctor_get(v___x_3002_, 2);
v_inferType_3007_ = lean_ctor_get(v___x_3002_, 3);
v_getLevel_3008_ = lean_ctor_get(v___x_3002_, 4);
v_congrInfo_3009_ = lean_ctor_get(v___x_3002_, 5);
v_defEqI_3010_ = lean_ctor_get(v___x_3002_, 6);
v_extensions_3011_ = lean_ctor_get(v___x_3002_, 7);
v_issues_3012_ = lean_ctor_get(v___x_3002_, 8);
v_instanceOverrides_3013_ = lean_ctor_get(v___x_3002_, 10);
v_debug_3014_ = lean_ctor_get_uint8(v___x_3002_, sizeof(void*)*11);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3016_ = v___x_3002_;
v_isShared_3017_ = v_isSharedCheck_3035_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_instanceOverrides_3013_);
lean_inc(v_canon_3003_);
lean_inc(v_issues_3012_);
lean_inc(v_extensions_3011_);
lean_inc(v_defEqI_3010_);
lean_inc(v_congrInfo_3009_);
lean_inc(v_getLevel_3008_);
lean_inc(v_inferType_3007_);
lean_inc(v_proofInstInfo_3006_);
lean_inc(v_maxFVar_3005_);
lean_inc(v_share_3004_);
lean_dec(v___x_3002_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3035_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_cache_3018_; lean_object* v_cacheInType_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3034_; 
v_cache_3018_ = lean_ctor_get(v_canon_3003_, 0);
v_cacheInType_3019_ = lean_ctor_get(v_canon_3003_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_canon_3003_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3021_ = v_canon_3003_;
v_isShared_3022_ = v_isSharedCheck_3034_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_cacheInType_3019_);
lean_inc(v_cache_3018_);
lean_dec(v_canon_3003_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3034_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_inc(v_a_2998_);
v___x_3023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3019_, v_e_2714_, v_a_2998_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_cache_3018_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 9, v___x_3025_);
v___x_3027_ = v___x_3016_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_share_3004_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_maxFVar_3005_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_proofInstInfo_3006_);
lean_ctor_set(v_reuseFailAlloc_3032_, 3, v_inferType_3007_);
lean_ctor_set(v_reuseFailAlloc_3032_, 4, v_getLevel_3008_);
lean_ctor_set(v_reuseFailAlloc_3032_, 5, v_congrInfo_3009_);
lean_ctor_set(v_reuseFailAlloc_3032_, 6, v_defEqI_3010_);
lean_ctor_set(v_reuseFailAlloc_3032_, 7, v_extensions_3011_);
lean_ctor_set(v_reuseFailAlloc_3032_, 8, v_issues_3012_);
lean_ctor_set(v_reuseFailAlloc_3032_, 9, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3032_, 10, v_instanceOverrides_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3032_, sizeof(void*)*11, v_debug_3014_);
v___x_3027_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_st_ref_set(v_a_2717_, v___x_3027_);
if (v_isShared_3001_ == 0)
{
v___x_3030_ = v___x_3000_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_2998_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 4);
return v___x_2997_;
}
}
}
}
case 5:
{
if (v_a_2715_ == 0)
{
lean_object* v___x_3037_; lean_object* v_canon_3038_; lean_object* v_cache_3039_; lean_object* v___x_3040_; 
v___x_3037_ = lean_st_ref_get(v_a_2717_);
v_canon_3038_ = lean_ctor_get(v___x_3037_, 9);
lean_inc_ref(v_canon_3038_);
lean_dec(v___x_3037_);
v_cache_3039_ = lean_ctor_get(v_canon_3038_, 0);
lean_inc_ref(v_cache_3039_);
lean_dec_ref(v_canon_3038_);
v___x_3040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3039_, v_e_2714_);
lean_dec_ref(v_cache_3039_);
if (lean_obj_tag(v___x_3040_) == 1)
{
lean_object* v_val_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref_known(v_e_2714_, 2);
v_val_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_val_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set_tag(v___x_3043_, 0);
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_val_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_object* v___x_3049_; 
lean_dec(v___x_3040_);
lean_inc_ref(v_e_2714_);
v___x_3049_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3088_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3088_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3088_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v_canon_3055_; lean_object* v_share_3056_; lean_object* v_maxFVar_3057_; lean_object* v_proofInstInfo_3058_; lean_object* v_inferType_3059_; lean_object* v_getLevel_3060_; lean_object* v_congrInfo_3061_; lean_object* v_defEqI_3062_; lean_object* v_extensions_3063_; lean_object* v_issues_3064_; lean_object* v_instanceOverrides_3065_; uint8_t v_debug_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3087_; 
v___x_3054_ = lean_st_ref_take(v_a_2717_);
v_canon_3055_ = lean_ctor_get(v___x_3054_, 9);
v_share_3056_ = lean_ctor_get(v___x_3054_, 0);
v_maxFVar_3057_ = lean_ctor_get(v___x_3054_, 1);
v_proofInstInfo_3058_ = lean_ctor_get(v___x_3054_, 2);
v_inferType_3059_ = lean_ctor_get(v___x_3054_, 3);
v_getLevel_3060_ = lean_ctor_get(v___x_3054_, 4);
v_congrInfo_3061_ = lean_ctor_get(v___x_3054_, 5);
v_defEqI_3062_ = lean_ctor_get(v___x_3054_, 6);
v_extensions_3063_ = lean_ctor_get(v___x_3054_, 7);
v_issues_3064_ = lean_ctor_get(v___x_3054_, 8);
v_instanceOverrides_3065_ = lean_ctor_get(v___x_3054_, 10);
v_debug_3066_ = lean_ctor_get_uint8(v___x_3054_, sizeof(void*)*11);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3068_ = v___x_3054_;
v_isShared_3069_ = v_isSharedCheck_3087_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_instanceOverrides_3065_);
lean_inc(v_canon_3055_);
lean_inc(v_issues_3064_);
lean_inc(v_extensions_3063_);
lean_inc(v_defEqI_3062_);
lean_inc(v_congrInfo_3061_);
lean_inc(v_getLevel_3060_);
lean_inc(v_inferType_3059_);
lean_inc(v_proofInstInfo_3058_);
lean_inc(v_maxFVar_3057_);
lean_inc(v_share_3056_);
lean_dec(v___x_3054_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3087_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v_cache_3070_; lean_object* v_cacheInType_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3086_; 
v_cache_3070_ = lean_ctor_get(v_canon_3055_, 0);
v_cacheInType_3071_ = lean_ctor_get(v_canon_3055_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_canon_3055_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3073_ = v_canon_3055_;
v_isShared_3074_ = v_isSharedCheck_3086_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_cacheInType_3071_);
lean_inc(v_cache_3070_);
lean_dec(v_canon_3055_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3086_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_inc(v_a_3050_);
v___x_3075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3070_, v_e_2714_, v_a_3050_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3075_);
v___x_3077_ = v___x_3073_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_cacheInType_3071_);
v___x_3077_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3079_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 9, v___x_3077_);
v___x_3079_ = v___x_3068_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_share_3056_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_maxFVar_3057_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_proofInstInfo_3058_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_inferType_3059_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_getLevel_3060_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_congrInfo_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_defEqI_3062_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_extensions_3063_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_issues_3064_);
lean_ctor_set(v_reuseFailAlloc_3084_, 9, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3084_, 10, v_instanceOverrides_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*11, v_debug_3066_);
v___x_3079_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_st_ref_set(v_a_2717_, v___x_3079_);
if (v_isShared_3053_ == 0)
{
v___x_3082_ = v___x_3052_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3050_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 2);
return v___x_3049_;
}
}
}
else
{
lean_object* v___x_3089_; lean_object* v_canon_3090_; lean_object* v_cacheInType_3091_; lean_object* v___x_3092_; 
v___x_3089_ = lean_st_ref_get(v_a_2717_);
v_canon_3090_ = lean_ctor_get(v___x_3089_, 9);
lean_inc_ref(v_canon_3090_);
lean_dec(v___x_3089_);
v_cacheInType_3091_ = lean_ctor_get(v_canon_3090_, 1);
lean_inc_ref(v_cacheInType_3091_);
lean_dec_ref(v_canon_3090_);
v___x_3092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3091_, v_e_2714_);
lean_dec_ref(v_cacheInType_3091_);
if (lean_obj_tag(v___x_3092_) == 1)
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref_known(v_e_2714_, 2);
v_val_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 0);
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_val_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3092_);
lean_inc_ref(v_e_2714_);
v___x_3101_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3140_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3140_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3140_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v_canon_3107_; lean_object* v_share_3108_; lean_object* v_maxFVar_3109_; lean_object* v_proofInstInfo_3110_; lean_object* v_inferType_3111_; lean_object* v_getLevel_3112_; lean_object* v_congrInfo_3113_; lean_object* v_defEqI_3114_; lean_object* v_extensions_3115_; lean_object* v_issues_3116_; lean_object* v_instanceOverrides_3117_; uint8_t v_debug_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3139_; 
v___x_3106_ = lean_st_ref_take(v_a_2717_);
v_canon_3107_ = lean_ctor_get(v___x_3106_, 9);
v_share_3108_ = lean_ctor_get(v___x_3106_, 0);
v_maxFVar_3109_ = lean_ctor_get(v___x_3106_, 1);
v_proofInstInfo_3110_ = lean_ctor_get(v___x_3106_, 2);
v_inferType_3111_ = lean_ctor_get(v___x_3106_, 3);
v_getLevel_3112_ = lean_ctor_get(v___x_3106_, 4);
v_congrInfo_3113_ = lean_ctor_get(v___x_3106_, 5);
v_defEqI_3114_ = lean_ctor_get(v___x_3106_, 6);
v_extensions_3115_ = lean_ctor_get(v___x_3106_, 7);
v_issues_3116_ = lean_ctor_get(v___x_3106_, 8);
v_instanceOverrides_3117_ = lean_ctor_get(v___x_3106_, 10);
v_debug_3118_ = lean_ctor_get_uint8(v___x_3106_, sizeof(void*)*11);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3120_ = v___x_3106_;
v_isShared_3121_ = v_isSharedCheck_3139_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_instanceOverrides_3117_);
lean_inc(v_canon_3107_);
lean_inc(v_issues_3116_);
lean_inc(v_extensions_3115_);
lean_inc(v_defEqI_3114_);
lean_inc(v_congrInfo_3113_);
lean_inc(v_getLevel_3112_);
lean_inc(v_inferType_3111_);
lean_inc(v_proofInstInfo_3110_);
lean_inc(v_maxFVar_3109_);
lean_inc(v_share_3108_);
lean_dec(v___x_3106_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3139_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_cache_3122_; lean_object* v_cacheInType_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3138_; 
v_cache_3122_ = lean_ctor_get(v_canon_3107_, 0);
v_cacheInType_3123_ = lean_ctor_get(v_canon_3107_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_canon_3107_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3125_ = v_canon_3107_;
v_isShared_3126_ = v_isSharedCheck_3138_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_cacheInType_3123_);
lean_inc(v_cache_3122_);
lean_dec(v_canon_3107_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3138_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_inc(v_a_3102_);
v___x_3127_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3123_, v_e_2714_, v_a_3102_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_cache_3122_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3131_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 9, v___x_3129_);
v___x_3131_ = v___x_3120_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_share_3108_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_maxFVar_3109_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_proofInstInfo_3110_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_inferType_3111_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_getLevel_3112_);
lean_ctor_set(v_reuseFailAlloc_3136_, 5, v_congrInfo_3113_);
lean_ctor_set(v_reuseFailAlloc_3136_, 6, v_defEqI_3114_);
lean_ctor_set(v_reuseFailAlloc_3136_, 7, v_extensions_3115_);
lean_ctor_set(v_reuseFailAlloc_3136_, 8, v_issues_3116_);
lean_ctor_set(v_reuseFailAlloc_3136_, 9, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3136_, 10, v_instanceOverrides_3117_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*11, v_debug_3118_);
v___x_3131_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_st_ref_set(v_a_2717_, v___x_3131_);
if (v_isShared_3105_ == 0)
{
v___x_3134_ = v___x_3104_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3102_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 2);
return v___x_3101_;
}
}
}
}
case 11:
{
if (v_a_2715_ == 0)
{
lean_object* v___x_3141_; lean_object* v_canon_3142_; lean_object* v_cache_3143_; lean_object* v___x_3144_; 
v___x_3141_ = lean_st_ref_get(v_a_2717_);
v_canon_3142_ = lean_ctor_get(v___x_3141_, 9);
lean_inc_ref(v_canon_3142_);
lean_dec(v___x_3141_);
v_cache_3143_ = lean_ctor_get(v_canon_3142_, 0);
lean_inc_ref(v_cache_3143_);
lean_dec_ref(v_canon_3142_);
v___x_3144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3143_, v_e_2714_);
lean_dec_ref(v_cache_3143_);
if (lean_obj_tag(v___x_3144_) == 1)
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_val_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
else
{
lean_object* v___x_3153_; 
lean_dec(v___x_3144_);
lean_inc_ref(v_e_2714_);
v___x_3153_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3192_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3192_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3192_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v_canon_3159_; lean_object* v_share_3160_; lean_object* v_maxFVar_3161_; lean_object* v_proofInstInfo_3162_; lean_object* v_inferType_3163_; lean_object* v_getLevel_3164_; lean_object* v_congrInfo_3165_; lean_object* v_defEqI_3166_; lean_object* v_extensions_3167_; lean_object* v_issues_3168_; lean_object* v_instanceOverrides_3169_; uint8_t v_debug_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3191_; 
v___x_3158_ = lean_st_ref_take(v_a_2717_);
v_canon_3159_ = lean_ctor_get(v___x_3158_, 9);
v_share_3160_ = lean_ctor_get(v___x_3158_, 0);
v_maxFVar_3161_ = lean_ctor_get(v___x_3158_, 1);
v_proofInstInfo_3162_ = lean_ctor_get(v___x_3158_, 2);
v_inferType_3163_ = lean_ctor_get(v___x_3158_, 3);
v_getLevel_3164_ = lean_ctor_get(v___x_3158_, 4);
v_congrInfo_3165_ = lean_ctor_get(v___x_3158_, 5);
v_defEqI_3166_ = lean_ctor_get(v___x_3158_, 6);
v_extensions_3167_ = lean_ctor_get(v___x_3158_, 7);
v_issues_3168_ = lean_ctor_get(v___x_3158_, 8);
v_instanceOverrides_3169_ = lean_ctor_get(v___x_3158_, 10);
v_debug_3170_ = lean_ctor_get_uint8(v___x_3158_, sizeof(void*)*11);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3172_ = v___x_3158_;
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_instanceOverrides_3169_);
lean_inc(v_canon_3159_);
lean_inc(v_issues_3168_);
lean_inc(v_extensions_3167_);
lean_inc(v_defEqI_3166_);
lean_inc(v_congrInfo_3165_);
lean_inc(v_getLevel_3164_);
lean_inc(v_inferType_3163_);
lean_inc(v_proofInstInfo_3162_);
lean_inc(v_maxFVar_3161_);
lean_inc(v_share_3160_);
lean_dec(v___x_3158_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_cache_3174_; lean_object* v_cacheInType_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3190_; 
v_cache_3174_ = lean_ctor_get(v_canon_3159_, 0);
v_cacheInType_3175_ = lean_ctor_get(v_canon_3159_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_canon_3159_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3177_ = v_canon_3159_;
v_isShared_3178_ = v_isSharedCheck_3190_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_cacheInType_3175_);
lean_inc(v_cache_3174_);
lean_dec(v_canon_3159_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3190_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc(v_a_3154_);
v___x_3179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3174_, v_e_2714_, v_a_3154_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_cacheInType_3175_);
v___x_3181_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 9, v___x_3181_);
v___x_3183_ = v___x_3172_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_share_3160_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_maxFVar_3161_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_proofInstInfo_3162_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_inferType_3163_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_getLevel_3164_);
lean_ctor_set(v_reuseFailAlloc_3188_, 5, v_congrInfo_3165_);
lean_ctor_set(v_reuseFailAlloc_3188_, 6, v_defEqI_3166_);
lean_ctor_set(v_reuseFailAlloc_3188_, 7, v_extensions_3167_);
lean_ctor_set(v_reuseFailAlloc_3188_, 8, v_issues_3168_);
lean_ctor_set(v_reuseFailAlloc_3188_, 9, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3188_, 10, v_instanceOverrides_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*11, v_debug_3170_);
v___x_3183_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = lean_st_ref_set(v_a_2717_, v___x_3183_);
if (v_isShared_3157_ == 0)
{
v___x_3186_ = v___x_3156_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3154_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_3153_;
}
}
}
else
{
lean_object* v___x_3193_; lean_object* v_canon_3194_; lean_object* v_cacheInType_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_st_ref_get(v_a_2717_);
v_canon_3194_ = lean_ctor_get(v___x_3193_, 9);
lean_inc_ref(v_canon_3194_);
lean_dec(v___x_3193_);
v_cacheInType_3195_ = lean_ctor_get(v_canon_3194_, 1);
lean_inc_ref(v_cacheInType_3195_);
lean_dec_ref(v_canon_3194_);
v___x_3196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3195_, v_e_2714_);
lean_dec_ref(v_cacheInType_3195_);
if (lean_obj_tag(v___x_3196_) == 1)
{
lean_object* v_val_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref_known(v_e_2714_, 3);
v_val_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_val_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 0);
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_val_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_object* v___x_3205_; 
lean_dec(v___x_3196_);
lean_inc_ref(v_e_2714_);
v___x_3205_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3244_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3244_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3244_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_canon_3211_; lean_object* v_share_3212_; lean_object* v_maxFVar_3213_; lean_object* v_proofInstInfo_3214_; lean_object* v_inferType_3215_; lean_object* v_getLevel_3216_; lean_object* v_congrInfo_3217_; lean_object* v_defEqI_3218_; lean_object* v_extensions_3219_; lean_object* v_issues_3220_; lean_object* v_instanceOverrides_3221_; uint8_t v_debug_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3243_; 
v___x_3210_ = lean_st_ref_take(v_a_2717_);
v_canon_3211_ = lean_ctor_get(v___x_3210_, 9);
v_share_3212_ = lean_ctor_get(v___x_3210_, 0);
v_maxFVar_3213_ = lean_ctor_get(v___x_3210_, 1);
v_proofInstInfo_3214_ = lean_ctor_get(v___x_3210_, 2);
v_inferType_3215_ = lean_ctor_get(v___x_3210_, 3);
v_getLevel_3216_ = lean_ctor_get(v___x_3210_, 4);
v_congrInfo_3217_ = lean_ctor_get(v___x_3210_, 5);
v_defEqI_3218_ = lean_ctor_get(v___x_3210_, 6);
v_extensions_3219_ = lean_ctor_get(v___x_3210_, 7);
v_issues_3220_ = lean_ctor_get(v___x_3210_, 8);
v_instanceOverrides_3221_ = lean_ctor_get(v___x_3210_, 10);
v_debug_3222_ = lean_ctor_get_uint8(v___x_3210_, sizeof(void*)*11);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3224_ = v___x_3210_;
v_isShared_3225_ = v_isSharedCheck_3243_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_instanceOverrides_3221_);
lean_inc(v_canon_3211_);
lean_inc(v_issues_3220_);
lean_inc(v_extensions_3219_);
lean_inc(v_defEqI_3218_);
lean_inc(v_congrInfo_3217_);
lean_inc(v_getLevel_3216_);
lean_inc(v_inferType_3215_);
lean_inc(v_proofInstInfo_3214_);
lean_inc(v_maxFVar_3213_);
lean_inc(v_share_3212_);
lean_dec(v___x_3210_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3243_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_cache_3226_; lean_object* v_cacheInType_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3242_; 
v_cache_3226_ = lean_ctor_get(v_canon_3211_, 0);
v_cacheInType_3227_ = lean_ctor_get(v_canon_3211_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_canon_3211_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3229_ = v_canon_3211_;
v_isShared_3230_ = v_isSharedCheck_3242_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_cacheInType_3227_);
lean_inc(v_cache_3226_);
lean_dec(v_canon_3211_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3242_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_inc(v_a_3206_);
v___x_3231_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3227_, v_e_2714_, v_a_3206_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 1, v___x_3231_);
v___x_3233_ = v___x_3229_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_cache_3226_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3235_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 9, v___x_3233_);
v___x_3235_ = v___x_3224_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_share_3212_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_maxFVar_3213_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_proofInstInfo_3214_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_inferType_3215_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v_getLevel_3216_);
lean_ctor_set(v_reuseFailAlloc_3240_, 5, v_congrInfo_3217_);
lean_ctor_set(v_reuseFailAlloc_3240_, 6, v_defEqI_3218_);
lean_ctor_set(v_reuseFailAlloc_3240_, 7, v_extensions_3219_);
lean_ctor_set(v_reuseFailAlloc_3240_, 8, v_issues_3220_);
lean_ctor_set(v_reuseFailAlloc_3240_, 9, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3240_, 10, v_instanceOverrides_3221_);
lean_ctor_set_uint8(v_reuseFailAlloc_3240_, sizeof(void*)*11, v_debug_3222_);
v___x_3235_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_st_ref_set(v_a_2717_, v___x_3235_);
if (v_isShared_3209_ == 0)
{
v___x_3238_ = v___x_3208_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3206_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 3);
return v___x_3205_;
}
}
}
}
case 10:
{
lean_object* v_data_3245_; lean_object* v_expr_3246_; lean_object* v___x_3247_; 
v_data_3245_ = lean_ctor_get(v_e_2714_, 0);
v_expr_3246_ = lean_ctor_get(v_e_2714_, 1);
lean_inc_ref(v_expr_3246_);
v___x_3247_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3246_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3262_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3262_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3262_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
size_t v___x_3252_; size_t v___x_3253_; uint8_t v___x_3254_; 
v___x_3252_ = lean_ptr_addr(v_expr_3246_);
v___x_3253_ = lean_ptr_addr(v_a_3248_);
v___x_3254_ = lean_usize_dec_eq(v___x_3252_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_inc(v_data_3245_);
lean_dec_ref_known(v_e_2714_, 2);
v___x_3255_ = l_Lean_Expr_mdata___override(v_data_3245_, v_a_3248_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3255_);
v___x_3257_ = v___x_3250_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
else
{
lean_object* v___x_3260_; 
lean_dec(v_a_3248_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v_e_2714_);
v___x_3260_ = v___x_3250_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_e_2714_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2714_, 2);
return v___x_3247_;
}
}
default: 
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_e_2714_);
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3264_, uint8_t v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
if (v_a_3265_ == 0)
{
lean_object* v___x_3273_; 
lean_inc_ref(v_e_3264_);
v___x_3273_ = l_Lean_Meta_isProp(v_e_3264_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; uint8_t v___x_3275_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v___x_3275_ = lean_unbox(v_a_3274_);
lean_dec(v_a_3274_);
if (v___x_3275_ == 0)
{
uint8_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = 1;
v___x_3277_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3264_, v___x_3276_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3278_;
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v_e_3264_);
v_a_3279_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3273_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3273_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
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
else
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3288_, lean_object* v_body_3289_, lean_object* v_x_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v___y_67153__boxed_3299_; lean_object* v_res_3300_; 
v___y_67153__boxed_3299_ = lean_unbox(v___y_3291_);
v_res_3300_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3288_, v_body_3289_, v_x_3290_, v___y_67153__boxed_3299_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3301_, lean_object* v_e_3302_, uint8_t v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
if (lean_obj_tag(v_e_3302_) == 7)
{
lean_object* v_binderName_3311_; lean_object* v_binderType_3312_; lean_object* v_body_3313_; uint8_t v_binderInfo_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_binderName_3311_ = lean_ctor_get(v_e_3302_, 0);
lean_inc(v_binderName_3311_);
v_binderType_3312_ = lean_ctor_get(v_e_3302_, 1);
lean_inc_ref(v_binderType_3312_);
v_body_3313_ = lean_ctor_get(v_e_3302_, 2);
lean_inc_ref(v_body_3313_);
v_binderInfo_3314_ = lean_ctor_get_uint8(v_e_3302_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3302_, 3);
v___x_3315_ = lean_expr_instantiate_rev(v_binderType_3312_, v_fvars_3301_);
lean_dec_ref(v_binderType_3312_);
v___x_3316_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3315_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___f_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___f_3318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3318_, 0, v_fvars_3301_);
lean_closure_set(v___f_3318_, 1, v_body_3313_);
v___x_3319_ = 0;
v___x_3320_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3311_, v_binderInfo_3314_, v_a_3317_, v___f_3318_, v___x_3319_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3320_;
}
else
{
lean_dec_ref(v_body_3313_);
lean_dec(v_binderName_3311_);
lean_dec_ref(v_fvars_3301_);
return v___x_3316_;
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_expr_instantiate_rev(v_e_3302_, v_fvars_3301_);
lean_dec_ref(v_e_3302_);
v___x_3322_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3321_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; uint8_t v___x_3324_; uint8_t v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = 0;
v___x_3325_ = 1;
v___x_3326_ = 1;
v___x_3327_ = l_Lean_Meta_mkForallFVars(v_fvars_3301_, v_a_3323_, v___x_3324_, v___x_3325_, v___x_3325_, v___x_3326_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec_ref(v_fvars_3301_);
return v___x_3327_;
}
else
{
lean_dec_ref(v_fvars_3301_);
return v___x_3322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3328_, lean_object* v_body_3329_, lean_object* v_x_3330_, uint8_t v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = lean_array_push(v_fvars_3328_, v_x_3330_);
v___x_3340_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3339_, v_body_3329_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
uint8_t v_a_boxed_3350_; lean_object* v_res_3351_; 
v_a_boxed_3350_ = lean_unbox(v_a_3342_);
v_res_3351_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3341_, v_a_boxed_3350_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
uint8_t v_a_boxed_3361_; lean_object* v_res_3362_; 
v_a_boxed_3361_ = lean_unbox(v_a_3353_);
v_res_3362_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3352_, v_a_boxed_3361_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
uint8_t v_a_boxed_3372_; lean_object* v_res_3373_; 
v_a_boxed_3372_ = lean_unbox(v_a_3364_);
v_res_3373_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3363_, v_a_boxed_3372_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
uint8_t v_a_boxed_3383_; lean_object* v_res_3384_; 
v_a_boxed_3383_ = lean_unbox(v_a_3375_);
v_res_3384_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3374_, v_a_boxed_3383_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
uint8_t v_a_boxed_3394_; lean_object* v_res_3395_; 
v_a_boxed_3394_ = lean_unbox(v_a_3386_);
v_res_3395_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3385_, v_a_boxed_3394_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3396_, lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
uint8_t v_a_boxed_3406_; lean_object* v_res_3407_; 
v_a_boxed_3406_ = lean_unbox(v_a_3398_);
v_res_3407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3396_, v_e_3397_, v_a_boxed_3406_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3408_, lean_object* v_e_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
uint8_t v_a_boxed_3418_; lean_object* v_res_3419_; 
v_a_boxed_3418_ = lean_unbox(v_a_3410_);
v_res_3419_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3408_, v_e_3409_, v_a_boxed_3418_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3420_, lean_object* v_report_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
uint8_t v_report_boxed_3430_; uint8_t v_a_boxed_3431_; lean_object* v_res_3432_; 
v_report_boxed_3430_ = lean_unbox(v_report_3421_);
v_a_boxed_3431_ = lean_unbox(v_a_3422_);
v_res_3432_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3420_, v_report_boxed_3430_, v_a_boxed_3431_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
uint8_t v_a_boxed_3442_; lean_object* v_res_3443_; 
v_a_boxed_3442_ = lean_unbox(v_a_3434_);
v_res_3443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3433_, v_a_boxed_3442_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3444_, lean_object* v_e_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
uint8_t v_a_boxed_3454_; lean_object* v_res_3455_; 
v_a_boxed_3454_ = lean_unbox(v_a_3446_);
v_res_3455_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3444_, v_e_3445_, v_a_boxed_3454_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3456_, lean_object* v_00_u03b1_3457_, lean_object* v_c_3458_, lean_object* v_a_3459_, lean_object* v_b_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
uint8_t v_a_boxed_3469_; lean_object* v_res_3470_; 
v_a_boxed_3469_ = lean_unbox(v_a_3461_);
v_res_3470_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3456_, v_00_u03b1_3457_, v_c_3458_, v_a_3459_, v_b_3460_, v_a_boxed_3469_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3471_, lean_object* v_00_u03b1_3472_, lean_object* v_c_3473_, lean_object* v_inst_3474_, lean_object* v_a_3475_, lean_object* v_b_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
uint8_t v_a_boxed_3485_; lean_object* v_res_3486_; 
v_a_boxed_3485_ = lean_unbox(v_a_3477_);
v_res_3486_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3471_, v_00_u03b1_3472_, v_c_3473_, v_inst_3474_, v_a_3475_, v_b_3476_, v_a_boxed_3485_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
uint8_t v_a_boxed_3496_; lean_object* v_res_3497_; 
v_a_boxed_3496_ = lean_unbox(v_a_3488_);
v_res_3497_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3487_, v_a_boxed_3496_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
uint8_t v_a_boxed_3507_; lean_object* v_res_3508_; 
v_a_boxed_3507_ = lean_unbox(v_a_3499_);
v_res_3508_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3498_, v_a_boxed_3507_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3509_, lean_object* v_prop_3510_, lean_object* v_inst_3511_, lean_object* v_e_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
uint8_t v_a_boxed_3521_; lean_object* v_res_3522_; 
v_a_boxed_3521_ = lean_unbox(v_a_3513_);
v_res_3522_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3509_, v_prop_3510_, v_inst_3511_, v_e_3512_, v_a_boxed_3521_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3523_, lean_object* v_report_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
uint8_t v_report_boxed_3533_; uint8_t v_a_boxed_3534_; lean_object* v_res_3535_; 
v_report_boxed_3533_ = lean_unbox(v_report_3524_);
v_a_boxed_3534_ = lean_unbox(v_a_3525_);
v_res_3535_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3523_, v_report_boxed_3533_, v_a_boxed_3534_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3536_, lean_object* v_prop_3537_, lean_object* v_h_3538_, lean_object* v_e_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
uint8_t v_a_boxed_3548_; lean_object* v_res_3549_; 
v_a_boxed_3548_ = lean_unbox(v_a_3540_);
v_res_3549_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3536_, v_prop_3537_, v_h_3538_, v_e_3539_, v_a_boxed_3548_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
uint8_t v_a_boxed_3559_; lean_object* v_res_3560_; 
v_a_boxed_3559_ = lean_unbox(v_a_3551_);
v_res_3560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3550_, v_a_boxed_3559_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3561_, lean_object* v___x_3562_, lean_object* v_a_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v___y_67580__boxed_3573_; lean_object* v_res_3574_; 
v___y_67580__boxed_3573_ = lean_unbox(v___y_3565_);
v_res_3574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3561_, v___x_3562_, v_a_3563_, v_b_3564_, v___y_67580__boxed_3573_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___x_3562_);
lean_dec(v_upperBound_3561_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3575_, lean_object* v_a_3576_, lean_object* v___x_3577_, lean_object* v_snd_3578_, lean_object* v___x_3579_, lean_object* v_fst_3580_, lean_object* v_____r_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v___x_67645__boxed_3590_; uint8_t v___y_67647__boxed_3591_; lean_object* v_res_3592_; 
v___x_67645__boxed_3590_ = lean_unbox(v___x_3579_);
v___y_67647__boxed_3591_ = lean_unbox(v___y_3582_);
v_res_3592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3575_, v_a_3576_, v___x_3577_, v_snd_3578_, v___x_67645__boxed_3590_, v_fst_3580_, v_____r_3581_, v___y_67647__boxed_3591_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v_a_3576_);
lean_dec_ref(v___x_3575_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3593_, lean_object* v_prop_3594_, lean_object* v_h_3595_, lean_object* v_e_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
uint8_t v_a_boxed_3605_; lean_object* v_res_3606_; 
v_a_boxed_3605_ = lean_unbox(v_a_3597_);
v_res_3606_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3593_, v_prop_3594_, v_h_3595_, v_e_3596_, v_a_boxed_3605_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v___y_67771__boxed_3619_; lean_object* v_res_3620_; 
v___y_67771__boxed_3619_ = lean_unbox(v___y_3611_);
v_res_3620_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3607_, v_x_3608_, v_x_3609_, v_x_3610_, v___y_67771__boxed_3619_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
uint8_t v_a_boxed_3630_; lean_object* v_res_3631_; 
v_a_boxed_3630_ = lean_unbox(v_a_3622_);
v_res_3631_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3621_, v_a_boxed_3630_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3632_, uint8_t v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3632_, v___y_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v___y_70109__boxed_3651_; lean_object* v_res_3652_; 
v___y_70109__boxed_3651_ = lean_unbox(v___y_3643_);
v_res_3652_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3642_, v___y_70109__boxed_3651_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3653_, lean_object* v_name_3654_, lean_object* v_type_3655_, lean_object* v_val_3656_, lean_object* v_k_3657_, uint8_t v_nondep_3658_, uint8_t v_kind_3659_, uint8_t v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3654_, v_type_3655_, v_val_3656_, v_k_3657_, v_nondep_3658_, v_kind_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_name_3670_, lean_object* v_type_3671_, lean_object* v_val_3672_, lean_object* v_k_3673_, lean_object* v_nondep_3674_, lean_object* v_kind_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
uint8_t v_nondep_boxed_3684_; uint8_t v_kind_boxed_3685_; uint8_t v___y_70135__boxed_3686_; lean_object* v_res_3687_; 
v_nondep_boxed_3684_ = lean_unbox(v_nondep_3674_);
v_kind_boxed_3685_ = lean_unbox(v_kind_3675_);
v___y_70135__boxed_3686_ = lean_unbox(v___y_3676_);
v_res_3687_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3669_, v_name_3670_, v_type_3671_, v_val_3672_, v_k_3673_, v_nondep_boxed_3684_, v_kind_boxed_3685_, v___y_70135__boxed_3686_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3688_, lean_object* v_name_3689_, uint8_t v_bi_3690_, lean_object* v_type_3691_, lean_object* v_k_3692_, uint8_t v_kind_3693_, uint8_t v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3689_, v_bi_3690_, v_type_3691_, v_k_3692_, v_kind_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_name_3704_, lean_object* v_bi_3705_, lean_object* v_type_3706_, lean_object* v_k_3707_, lean_object* v_kind_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v_bi_boxed_3717_; uint8_t v_kind_boxed_3718_; uint8_t v___y_70161__boxed_3719_; lean_object* v_res_3720_; 
v_bi_boxed_3717_ = lean_unbox(v_bi_3705_);
v_kind_boxed_3718_ = lean_unbox(v_kind_3708_);
v___y_70161__boxed_3719_ = lean_unbox(v___y_3709_);
v_res_3720_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3703_, v_name_3704_, v_bi_boxed_3717_, v_type_3706_, v_k_3707_, v_kind_boxed_3718_, v___y_70161__boxed_3719_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3721_, lean_object* v_m_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3722_, v_a_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3725_, lean_object* v_m_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3725_, v_m_3726_, v_a_3727_);
lean_dec_ref(v_a_3727_);
lean_dec_ref(v_m_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3729_, lean_object* v_m_3730_, lean_object* v_a_3731_, lean_object* v_b_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3730_, v_a_3731_, v_b_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3734_, lean_object* v_msg_3735_, uint8_t v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3734_, v_msg_3735_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3745_, lean_object* v_msg_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
uint8_t v___y_70191__boxed_3755_; lean_object* v_res_3756_; 
v___y_70191__boxed_3755_ = lean_unbox(v___y_3747_);
v_res_3756_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3745_, v_msg_3746_, v___y_70191__boxed_3755_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3757_, lean_object* v___x_3758_, lean_object* v___x_3759_, lean_object* v_inst_3760_, lean_object* v_R_3761_, lean_object* v_a_3762_, lean_object* v_b_3763_, lean_object* v_c_3764_, uint8_t v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3757_, v___x_3759_, v_a_3762_, v_b_3763_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3774_, lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v_inst_3777_, lean_object* v_R_3778_, lean_object* v_a_3779_, lean_object* v_b_3780_, lean_object* v_c_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v___y_70221__boxed_3790_; lean_object* v_res_3791_; 
v___y_70221__boxed_3790_ = lean_unbox(v___y_3782_);
v_res_3791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3774_, v___x_3775_, v___x_3776_, v_inst_3777_, v_R_3778_, v_a_3779_, v_b_3780_, v_c_3781_, v___y_70221__boxed_3790_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_upperBound_3774_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3792_, lean_object* v_a_3793_, lean_object* v_x_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3793_, v_x_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3796_, lean_object* v_a_3797_, lean_object* v_x_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3796_, v_a_3797_, v_x_3798_);
lean_dec(v_x_3798_);
lean_dec_ref(v_a_3797_);
return v_res_3799_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3800_, lean_object* v_a_3801_, lean_object* v_x_3802_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3801_, v_x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3804_, lean_object* v_a_3805_, lean_object* v_x_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3804_, v_a_3805_, v_x_3806_);
lean_dec(v_x_3806_);
lean_dec_ref(v_a_3805_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3809_, lean_object* v_data_3810_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3812_, lean_object* v_a_3813_, lean_object* v_b_3814_, lean_object* v_x_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3813_, v_b_3814_, v_x_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3817_, lean_object* v_i_3818_, lean_object* v_source_3819_, lean_object* v_target_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3818_, v_source_3819_, v_target_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3823_, v_x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3826_, lean_object* v_i_3827_, lean_object* v_arg_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3826_, v_i_3827_, v_arg_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3850_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3850_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3850_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_unbox(v_a_3835_);
lean_dec(v_a_3835_);
if (v___x_3839_ == 3)
{
uint8_t v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3840_ = 0;
v___x_3841_ = lean_box(v___x_3840_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3841_);
v___x_3843_ = v___x_3837_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
else
{
uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3845_ = 1;
v___x_3846_ = lean_box(v___x_3845_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3846_);
v___x_3848_ = v___x_3837_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v_a_3851_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3834_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3834_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3859_, lean_object* v_i_3860_, lean_object* v_arg_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3859_, v_i_3860_, v_arg_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_i_3860_);
lean_dec_ref(v_pinfos_3859_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3868_, lean_object* v_opts_3869_, lean_object* v_act_3870_, lean_object* v_decl_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_inc(v___y_3877_);
lean_inc_ref(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
lean_inc(v___y_3873_);
lean_inc_ref(v___y_3872_);
v___x_3879_ = lean_apply_6(v_act_3870_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
v___x_3880_ = l_Lean_profileitIOUnsafe___redArg(v_category_3868_, v_opts_3869_, v___x_3879_, v_decl_3871_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3881_, lean_object* v_opts_3882_, lean_object* v_act_3883_, lean_object* v_decl_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3881_, v_opts_3882_, v_act_3883_, v_decl_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec_ref(v_opts_3882_);
lean_dec_ref(v_category_3881_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3893_, lean_object* v_category_3894_, lean_object* v_opts_3895_, lean_object* v_act_3896_, lean_object* v_decl_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3894_, v_opts_3895_, v_act_3896_, v_decl_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3906_, lean_object* v_category_3907_, lean_object* v_opts_3908_, lean_object* v_act_3909_, lean_object* v_decl_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3906_, v_category_3907_, v_opts_3908_, v_act_3909_, v_decl_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec_ref(v_opts_3908_);
lean_dec_ref(v_category_3907_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3919_, lean_object* v_e_3920_, uint8_t v___x_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_keyedConfig_3929_; uint8_t v_trackZetaDelta_3930_; lean_object* v_zetaDeltaSet_3931_; lean_object* v_lctx_3932_; lean_object* v_localInstances_3933_; lean_object* v_defEqCtx_x3f_3934_; lean_object* v_synthPendingDepth_3935_; lean_object* v_customCanUnfoldPredicate_x3f_3936_; uint8_t v_univApprox_3937_; uint8_t v_inTypeClassResolution_3938_; uint8_t v_cacheInferType_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_keyedConfig_3929_ = lean_ctor_get(v___y_3924_, 0);
v_trackZetaDelta_3930_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*7);
v_zetaDeltaSet_3931_ = lean_ctor_get(v___y_3924_, 1);
v_lctx_3932_ = lean_ctor_get(v___y_3924_, 2);
v_localInstances_3933_ = lean_ctor_get(v___y_3924_, 3);
v_defEqCtx_x3f_3934_ = lean_ctor_get(v___y_3924_, 4);
v_synthPendingDepth_3935_ = lean_ctor_get(v___y_3924_, 5);
v_customCanUnfoldPredicate_x3f_3936_ = lean_ctor_get(v___y_3924_, 6);
v_univApprox_3937_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3938_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*7 + 2);
v_cacheInferType_3939_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3929_);
v___x_3940_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3919_, v_keyedConfig_3929_);
lean_inc(v_customCanUnfoldPredicate_x3f_3936_);
lean_inc(v_synthPendingDepth_3935_);
lean_inc(v_defEqCtx_x3f_3934_);
lean_inc_ref(v_localInstances_3933_);
lean_inc_ref(v_lctx_3932_);
lean_inc(v_zetaDeltaSet_3931_);
v___x_3941_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
lean_ctor_set(v___x_3941_, 1, v_zetaDeltaSet_3931_);
lean_ctor_set(v___x_3941_, 2, v_lctx_3932_);
lean_ctor_set(v___x_3941_, 3, v_localInstances_3933_);
lean_ctor_set(v___x_3941_, 4, v_defEqCtx_x3f_3934_);
lean_ctor_set(v___x_3941_, 5, v_synthPendingDepth_3935_);
lean_ctor_set(v___x_3941_, 6, v_customCanUnfoldPredicate_x3f_3936_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*7, v_trackZetaDelta_3930_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*7 + 1, v_univApprox_3937_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3938_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*7 + 3, v_cacheInferType_3939_);
v___x_3942_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3920_, v___x_3921_, v___y_3922_, v___y_3923_, v___x_3941_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec_ref_known(v___x_3941_, 7);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3943_, lean_object* v_e_3944_, lean_object* v___x_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v___x_1951__boxed_3953_; uint8_t v___x_1952__boxed_3954_; lean_object* v_res_3955_; 
v___x_1951__boxed_3953_ = lean_unbox(v___x_3943_);
v___x_1952__boxed_3954_ = lean_unbox(v___x_3945_);
v_res_3955_ = l_Lean_Meta_Sym_canon___lam__0(v___x_1951__boxed_3953_, v_e_3944_, v___x_1952__boxed_3954_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v_options_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___f_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_options_3965_ = lean_ctor_get(v_a_3962_, 2);
v___x_3966_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3967_ = 0;
v___x_3968_ = 2;
v___x_3969_ = lean_box(v___x_3968_);
v___x_3970_ = lean_box(v___x_3967_);
v___f_3971_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3971_, 0, v___x_3969_);
lean_closure_set(v___f_3971_, 1, v_e_3957_);
lean_closure_set(v___f_3971_, 2, v___x_3970_);
v___x_3972_ = lean_box(0);
v___x_3973_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3966_, v_options_3965_, v___f_3971_, v___x_3972_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_Meta_Sym_canon(v_e_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
return v_res_3982_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
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

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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_113_, v___y_112_);
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
v___y_110_ = v_modified_141_;
v___y_111_ = v_args_140_;
v___y_112_ = v___y_142_;
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
v___y_110_ = v_modified_141_;
v___y_111_ = v_args_140_;
v___y_112_ = v___y_142_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(uint8_t v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* v_x_389_){
_start:
{
uint8_t v_x_4__boxed_390_; lean_object* v_res_391_; 
v_x_4__boxed_390_ = lean_unbox(v_x_389_);
v_res_391_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(v_x_4__boxed_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_392_){
_start:
{
lean_inc(v_k_392_);
return v_k_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_393_);
lean_dec(v_k_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_395_, lean_object* v_ctorIdx_396_, uint8_t v_t_397_, lean_object* v_h_398_, lean_object* v_k_399_){
_start:
{
lean_inc(v_k_399_);
return v_k_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
uint8_t v_t_boxed_405_; lean_object* v_res_406_; 
v_t_boxed_405_ = lean_unbox(v_t_402_);
v_res_406_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_400_, v_ctorIdx_401_, v_t_boxed_405_, v_h_403_, v_k_404_);
lean_dec(v_k_404_);
lean_dec(v_ctorIdx_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_407_){
_start:
{
lean_inc(v_canonType_407_);
return v_canonType_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_408_);
lean_dec(v_canonType_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_410_, uint8_t v_t_411_, lean_object* v_h_412_, lean_object* v_canonType_413_){
_start:
{
lean_inc(v_canonType_413_);
return v_canonType_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_canonType_417_){
_start:
{
uint8_t v_t_boxed_418_; lean_object* v_res_419_; 
v_t_boxed_418_ = lean_unbox(v_t_415_);
v_res_419_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_414_, v_t_boxed_418_, v_h_416_, v_canonType_417_);
lean_dec(v_canonType_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_420_){
_start:
{
lean_inc(v_canonInst_420_);
return v_canonInst_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_421_);
lean_dec(v_canonInst_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_423_, uint8_t v_t_424_, lean_object* v_h_425_, lean_object* v_canonInst_426_){
_start:
{
lean_inc(v_canonInst_426_);
return v_canonInst_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_canonInst_430_){
_start:
{
uint8_t v_t_boxed_431_; lean_object* v_res_432_; 
v_t_boxed_431_ = lean_unbox(v_t_428_);
v_res_432_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_427_, v_t_boxed_431_, v_h_429_, v_canonInst_430_);
lean_dec(v_canonInst_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_433_){
_start:
{
lean_inc(v_canonImplicit_433_);
return v_canonImplicit_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_434_);
lean_dec(v_canonImplicit_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_436_, uint8_t v_t_437_, lean_object* v_h_438_, lean_object* v_canonImplicit_439_){
_start:
{
lean_inc(v_canonImplicit_439_);
return v_canonImplicit_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_canonImplicit_443_){
_start:
{
uint8_t v_t_boxed_444_; lean_object* v_res_445_; 
v_t_boxed_444_ = lean_unbox(v_t_441_);
v_res_445_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_440_, v_t_boxed_444_, v_h_442_, v_canonImplicit_443_);
lean_dec(v_canonImplicit_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_446_){
_start:
{
lean_inc(v_visit_446_);
return v_visit_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_447_);
lean_dec(v_visit_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_449_, uint8_t v_t_450_, lean_object* v_h_451_, lean_object* v_visit_452_){
_start:
{
lean_inc(v_visit_452_);
return v_visit_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_visit_456_){
_start:
{
uint8_t v_t_boxed_457_; lean_object* v_res_458_; 
v_t_boxed_457_ = lean_unbox(v_t_454_);
v_res_458_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_453_, v_t_boxed_457_, v_h_455_, v_visit_456_);
lean_dec(v_visit_456_);
return v_res_458_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_473_, lean_object* v_x_474_){
_start:
{
switch(v_r_473_)
{
case 0:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_475_;
}
case 1:
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_476_;
}
case 2:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_477_;
}
default: 
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_479_, lean_object* v_x_480_){
_start:
{
uint8_t v_r_boxed_481_; lean_object* v_res_482_; 
v_r_boxed_481_ = lean_unbox(v_r_479_);
v_res_482_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_481_, v_x_480_);
lean_dec(v_x_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_485_, lean_object* v_i_486_, lean_object* v_arg_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_array_get_size(v_pinfos_485_);
v___x_544_ = lean_nat_dec_lt(v_i_486_, v___x_543_);
if (v___x_544_ == 0)
{
v___y_494_ = v_a_488_;
v___y_495_ = v_a_489_;
v___y_496_ = v_a_490_;
v___y_497_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v_pinfo_545_; uint8_t v_isInstance_546_; 
v_pinfo_545_ = lean_array_fget_borrowed(v_pinfos_485_, v_i_486_);
v_isInstance_546_ = lean_ctor_get_uint8(v_pinfo_545_, sizeof(void*)*1 + 4);
if (v_isInstance_546_ == 0)
{
uint8_t v_isProp_547_; 
v_isProp_547_ = lean_ctor_get_uint8(v_pinfo_545_, sizeof(void*)*1 + 2);
if (v_isProp_547_ == 0)
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_545_);
if (v___x_548_ == 0)
{
v___y_494_ = v_a_488_;
v___y_495_ = v_a_489_;
v___y_496_ = v_a_490_;
v___y_497_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_isTypeFormer(v_arg_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_565_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_565_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_565_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_565_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_unbox(v_a_550_);
lean_dec(v_a_550_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = 2;
v___x_556_ = lean_box(v___x_555_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_556_);
v___x_558_ = v___x_552_;
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
else
{
uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_560_ = 0;
v___x_561_ = lean_box(v___x_560_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_561_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_a_566_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_549_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_549_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_arg_487_);
v___x_574_ = 3;
v___x_575_ = lean_box(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
else
{
uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_arg_487_);
v___x_577_ = 1;
v___x_578_ = lean_box(v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
v___jp_493_:
{
lean_object* v___x_498_; 
lean_inc_ref(v_arg_487_);
v___x_498_ = l_Lean_Meta_isProp(v_arg_487_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_534_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_534_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_534_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_534_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___x_503_; 
v___x_503_ = lean_unbox(v_a_499_);
lean_dec(v_a_499_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_del_object(v___x_501_);
v___x_504_ = l_Lean_Meta_isTypeFormer(v_arg_487_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_520_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_520_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_520_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_520_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; 
v___x_509_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = 3;
v___x_511_ = lean_box(v___x_510_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
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
else
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = 0;
v___x_516_ = lean_box(v___x_515_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_516_);
v___x_518_ = v___x_507_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_a_521_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_504_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_504_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_dec_ref(v_arg_487_);
v___x_529_ = 3;
v___x_530_ = lean_box(v___x_529_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_530_);
v___x_532_ = v___x_501_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_arg_487_);
v_a_535_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_498_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_498_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_580_, lean_object* v_i_581_, lean_object* v_arg_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_580_, v_i_581_, v_arg_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_i_581_);
lean_dec_ref(v_pinfos_580_);
return v_res_588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_589_; lean_object* v_dummy_590_; 
v___x_589_ = lean_box(0);
v_dummy_590_ = l_Lean_Expr_sort___override(v___x_589_);
return v_dummy_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_591_, lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
uint8_t v_fromClass_598_; 
v_fromClass_598_ = lean_ctor_get_uint8(v_info_591_, sizeof(void*)*3);
if (v_fromClass_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_592_, v_fromClass_598_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_635_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_635_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_635_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_635_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
if (lean_obj_tag(v_a_600_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_del_object(v___x_602_);
v_val_604_ = lean_ctor_get(v_a_600_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_a_600_, 1);
v___x_605_ = l_Lean_Expr_getAppFn(v_val_604_);
v___x_606_ = l_Lean_Meta_reduceProj_x3f(v___x_605_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
if (lean_obj_tag(v_a_607_) == 0)
{
lean_dec(v_val_604_);
return v___x_606_;
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_629_; 
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_630_);
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_628_; 
v_val_611_ = lean_ctor_get(v_a_607_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_628_ == 0)
{
v___x_613_ = v_a_607_;
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_a_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_dummy_615_; lean_object* v_nargs_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_dummy_615_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_616_ = l_Lean_Expr_getAppNumArgs(v_val_604_);
lean_inc(v_nargs_616_);
v___x_617_ = lean_mk_array(v_nargs_616_, v_dummy_615_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_sub(v_nargs_616_, v___x_618_);
lean_dec(v_nargs_616_);
v___x_620_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_604_, v___x_617_, v___x_619_);
v___x_621_ = l_Lean_mkAppN(v_val_611_, v___x_620_);
lean_dec_ref(v___x_620_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_621_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_623_);
v___x_625_ = v___x_609_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_dec(v_val_604_);
return v___x_606_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec(v_a_600_);
v___x_631_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_631_);
v___x_633_ = v___x_602_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
return v___x_599_;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec_ref(v_e_592_);
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_638_, lean_object* v_e_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_638_, v_e_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec_ref(v_info_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_646_, lean_object* v_e_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_646_, v_e_647_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_656_, lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_656_, v_e_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec_ref(v_info_656_);
return v_res_665_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_668_ = l_Lean_Expr_isConstOf(v_e_666_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_669_);
lean_dec_ref(v_e_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = l_Lean_Expr_cleanupAnnotations(v_e_705_);
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_708_ = l_Lean_Expr_isConstOf(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_Expr_isApp(v___x_706_);
if (v___x_709_ == 0)
{
lean_dec_ref(v___x_706_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_706_);
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_712_ = l_Lean_Expr_isConstOf(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_Expr_isApp(v___x_710_);
if (v___x_713_ == 0)
{
lean_dec_ref(v___x_710_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_710_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_dec_ref(v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_dec_ref(v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_720_);
return v___x_721_;
}
else
{
lean_object* v_arg_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_arg_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_arg_722_);
v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_725_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_727_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_729_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_731_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_733_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_732_);
lean_dec_ref(v___x_723_);
if (v___x_733_ == 0)
{
lean_dec_ref(v_arg_722_);
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
v___x_734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_722_);
lean_dec_ref(v_arg_722_);
return v___x_734_;
}
}
else
{
uint8_t v___x_735_; 
lean_dec_ref(v___x_723_);
v___x_735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_722_);
lean_dec_ref(v_arg_722_);
return v___x_735_;
}
}
else
{
uint8_t v___x_736_; 
lean_dec_ref(v___x_723_);
v___x_736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_722_);
lean_dec_ref(v_arg_722_);
return v___x_736_;
}
}
else
{
uint8_t v___x_737_; 
lean_dec_ref(v___x_723_);
v___x_737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_722_);
lean_dec_ref(v_arg_722_);
return v___x_737_;
}
}
else
{
uint8_t v___x_738_; 
lean_dec_ref(v___x_723_);
v___x_738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_722_);
lean_dec_ref(v_arg_722_);
return v___x_738_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_710_);
return v___x_712_;
}
}
}
else
{
lean_dec_ref(v___x_706_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_748_, lean_object* v_inst_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v_inst_749_);
lean_inc_ref(v_e_748_);
v___x_757_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_748_, v_inst_749_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_808_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_808_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_808_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_808_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = lean_unbox(v_a_758_);
lean_dec(v_a_758_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_del_object(v___x_760_);
v___x_763_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_750_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_796_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_796_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_796_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_796_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v_verbose_768_; 
v_verbose_768_ = lean_ctor_get_uint8(v_a_764_, 0);
lean_dec(v_a_764_);
if (v_verbose_768_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v_inst_749_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v_e_748_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_e_748_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_del_object(v___x_766_);
v___x_772_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_748_);
v___x_773_ = l_Lean_indentExpr(v_e_748_);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_indentExpr(v_inst_749_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_Meta_Sym_reportIssue(v___x_778_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_787_);
v___x_781_ = v___x_779_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_dec(v___x_779_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_e_748_);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_e_748_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_e_748_);
v_a_788_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_779_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_779_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_e_748_);
v_a_797_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_763_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_763_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v_e_748_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_inst_749_);
v___x_806_ = v___x_760_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_inst_749_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_e_748_);
v_a_809_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_757_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_757_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_817_, lean_object* v_inst_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_817_, v_inst_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_830_ = lean_st_ref_get(v___y_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_env_831_);
lean_dec(v___x_830_);
v___x_832_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_831_, v_declName_827_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_834_, v___y_835_);
lean_dec(v___y_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_838_, uint8_t v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_838_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___y_4015__boxed_857_; lean_object* v_res_858_; 
v___y_4015__boxed_857_ = lean_unbox(v___y_849_);
v_res_858_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_848_, v___y_4015__boxed_857_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_859_, uint8_t v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v___x_868_; 
lean_inc_ref(v_e_859_);
v___x_868_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_859_);
if (v___x_868_ == 0)
{
lean_object* v_f_869_; 
v_f_869_ = l_Lean_Expr_getAppFn(v_e_859_);
if (lean_obj_tag(v_f_869_) == 4)
{
lean_object* v_declName_870_; lean_object* v___x_871_; lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_901_; 
v_declName_870_ = lean_ctor_get(v_f_869_, 0);
lean_inc(v_declName_870_);
lean_dec_ref_known(v_f_869_, 2);
v___x_871_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_870_, v_a_866_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_901_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_901_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_901_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 1)
{
lean_object* v_val_876_; lean_object* v___x_877_; 
lean_del_object(v___x_874_);
v_val_876_ = lean_ctor_get(v_a_872_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v_a_872_, 1);
lean_inc_ref(v_e_859_);
v___x_877_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_876_, v_e_859_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_val_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_889_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_889_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_889_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_889_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (lean_obj_tag(v_a_878_) == 0)
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_e_859_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_e_859_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; 
lean_dec_ref(v_e_859_);
v_val_885_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_a_878_, 1);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_val_885_);
v___x_887_ = v___x_880_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_val_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_e_859_);
v_a_890_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_877_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_877_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
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
lean_object* v___x_899_; 
lean_dec(v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_e_859_);
v___x_899_ = v___x_874_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_e_859_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec_ref(v_f_869_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_e_859_);
return v___x_902_;
}
}
else
{
lean_object* v___x_903_; 
lean_inc_ref(v_e_859_);
v___x_903_ = l_Lean_Meta_evalNat(v_e_859_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_934_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_934_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_934_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_934_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
if (lean_obj_tag(v_a_904_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec_ref(v_e_859_);
v_val_908_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_val_908_);
lean_dec_ref_known(v_a_904_, 1);
v___x_909_ = l_Lean_mkNatLit(v_val_908_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_913_; 
lean_del_object(v___x_906_);
lean_dec(v_a_904_);
lean_inc_ref(v_e_859_);
v___x_913_ = l_Lean_Meta_isOffset_x3f(v_e_859_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_925_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 1)
{
lean_object* v_val_918_; lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_921_; 
lean_del_object(v___x_916_);
lean_dec_ref(v_e_859_);
v_val_918_ = lean_ctor_get(v_a_914_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v_a_914_, 1);
v_fst_919_ = lean_ctor_get(v_val_918_, 0);
lean_inc(v_fst_919_);
v_snd_920_ = lean_ctor_get(v_val_918_, 1);
lean_inc(v_snd_920_);
lean_dec(v_val_918_);
v___x_921_ = l_Lean_Meta_mkOffset(v_fst_919_, v_snd_920_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_921_;
}
else
{
lean_object* v___x_923_; 
lean_dec(v_a_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_e_859_);
v___x_923_ = v___x_916_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_e_859_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_e_859_);
v_a_926_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_913_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_913_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_e_859_);
v_a_935_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_903_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_903_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_a_boxed_952_; lean_object* v_res_953_; 
v_a_boxed_952_ = lean_unbox(v_a_944_);
v_res_953_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_943_, v_a_boxed_952_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_957_, lean_object* v_type_958_, uint8_t v_report_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc_ref(v_type_958_);
v___x_967_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_958_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1019_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1019_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1019_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
if (lean_obj_tag(v_a_968_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_973_; 
lean_del_object(v___x_970_);
lean_dec_ref(v_type_958_);
v_val_972_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v_a_968_, 1);
v___x_973_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_957_, v_val_972_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_973_;
}
else
{
lean_dec(v_a_968_);
if (v_report_959_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v_type_958_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_e_957_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_e_957_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v___x_977_; 
lean_del_object(v___x_970_);
v___x_977_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_960_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1010_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1010_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1010_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
uint8_t v_verbose_982_; 
v_verbose_982_ = lean_ctor_get_uint8(v_a_978_, 0);
lean_dec(v_a_978_);
if (v_verbose_982_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v_type_958_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_e_957_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_e_957_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_980_);
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_957_);
v___x_987_ = l_Lean_indentExpr(v_e_957_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_indentExpr(v_type_958_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Meta_Sym_reportIssue(v___x_992_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1001_);
v___x_995_ = v___x_993_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_993_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v_e_957_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_e_957_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_e_957_);
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_type_958_);
lean_dec_ref(v_e_957_);
v_a_1011_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_977_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_977_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_type_958_);
lean_dec_ref(v_e_957_);
v_a_1020_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_967_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_967_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1028_, lean_object* v_type_1029_, lean_object* v_report_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
uint8_t v_report_boxed_1038_; lean_object* v_res_1039_; 
v_report_boxed_1038_ = lean_unbox(v_report_1030_);
v_res_1039_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1028_, v_type_1029_, v_report_boxed_1038_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1040_, lean_object* v_type_1041_, uint8_t v_report_1042_, uint8_t v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1040_, v_type_1041_, v_report_1042_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1052_, lean_object* v_type_1053_, lean_object* v_report_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
uint8_t v_report_boxed_1063_; uint8_t v_a_boxed_1064_; lean_object* v_res_1065_; 
v_report_boxed_1063_ = lean_unbox(v_report_1054_);
v_a_boxed_1064_ = lean_unbox(v_a_1055_);
v_res_1065_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1052_, v_type_1053_, v_report_boxed_1063_, v_a_boxed_1064_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
return v___x_1068_;
}
else
{
lean_object* v_key_1069_; lean_object* v_tail_1070_; uint8_t v___x_1071_; 
v_key_1069_ = lean_ctor_get(v_x_1067_, 0);
v_tail_1070_ = lean_ctor_get(v_x_1067_, 2);
v___x_1071_ = lean_expr_eqv(v_key_1069_, v_a_1066_);
if (v___x_1071_ == 0)
{
v_x_1067_ = v_tail_1070_;
goto _start;
}
else
{
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1073_, lean_object* v_x_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1073_, v_x_1074_);
lean_dec(v_x_1074_);
lean_dec_ref(v_a_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
return v_x_1077_;
}
else
{
lean_object* v_key_1079_; lean_object* v_value_1080_; lean_object* v_tail_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1104_; 
v_key_1079_ = lean_ctor_get(v_x_1078_, 0);
v_value_1080_ = lean_ctor_get(v_x_1078_, 1);
v_tail_1081_ = lean_ctor_get(v_x_1078_, 2);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1083_ = v_x_1078_;
v_isShared_1084_ = v_isSharedCheck_1104_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_tail_1081_);
lean_inc(v_value_1080_);
lean_inc(v_key_1079_);
lean_dec(v_x_1078_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1104_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v_fold_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1085_ = lean_array_get_size(v_x_1077_);
v___x_1086_ = l_Lean_Expr_hash(v_key_1079_);
v___x_1087_ = 32ULL;
v___x_1088_ = lean_uint64_shift_right(v___x_1086_, v___x_1087_);
v_fold_1089_ = lean_uint64_xor(v___x_1086_, v___x_1088_);
v___x_1090_ = 16ULL;
v___x_1091_ = lean_uint64_shift_right(v_fold_1089_, v___x_1090_);
v___x_1092_ = lean_uint64_xor(v_fold_1089_, v___x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = lean_usize_of_nat(v___x_1085_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_sub(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_usize_land(v___x_1093_, v___x_1096_);
v___x_1098_ = lean_array_uget_borrowed(v_x_1077_, v___x_1097_);
lean_inc(v___x_1098_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 2, v___x_1098_);
v___x_1100_ = v___x_1083_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_key_1079_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_value_1080_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_array_uset(v_x_1077_, v___x_1097_, v___x_1100_);
v_x_1077_ = v___x_1101_;
v_x_1078_ = v_tail_1081_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object* v_i_1105_, lean_object* v_source_1106_, lean_object* v_target_1107_){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_array_get_size(v_source_1106_);
v___x_1109_ = lean_nat_dec_lt(v_i_1105_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_dec_ref(v_source_1106_);
lean_dec(v_i_1105_);
return v_target_1107_;
}
else
{
lean_object* v_es_1110_; lean_object* v___x_1111_; lean_object* v_source_1112_; lean_object* v_target_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_es_1110_ = lean_array_fget(v_source_1106_, v_i_1105_);
v___x_1111_ = lean_box(0);
v_source_1112_ = lean_array_fset(v_source_1106_, v_i_1105_, v___x_1111_);
v_target_1113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_1107_, v_es_1110_);
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_add(v_i_1105_, v___x_1114_);
lean_dec(v_i_1105_);
v_i_1105_ = v___x_1115_;
v_source_1106_ = v_source_1112_;
v_target_1107_ = v_target_1113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_nbuckets_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1118_ = lean_array_get_size(v_data_1117_);
v___x_1119_ = lean_unsigned_to_nat(2u);
v_nbuckets_1120_ = lean_nat_mul(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_mk_array(v_nbuckets_1120_, v___x_1122_);
v___x_1124_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_1121_, v_data_1117_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_dec(v_b_1126_);
lean_dec_ref(v_a_1125_);
return v_x_1127_;
}
else
{
lean_object* v_key_1128_; lean_object* v_value_1129_; lean_object* v_tail_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1142_; 
v_key_1128_ = lean_ctor_get(v_x_1127_, 0);
v_value_1129_ = lean_ctor_get(v_x_1127_, 1);
v_tail_1130_ = lean_ctor_get(v_x_1127_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1132_ = v_x_1127_;
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_tail_1130_);
lean_inc(v_value_1129_);
lean_inc(v_key_1128_);
lean_dec(v_x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_expr_eqv(v_key_1128_, v_a_1125_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1125_, v_b_1126_, v_tail_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 2, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_key_1128_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_value_1129_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1140_; 
lean_dec(v_value_1129_);
lean_dec(v_key_1128_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v_b_1126_);
lean_ctor_set(v___x_1132_, 0, v_a_1125_);
v___x_1140_ = v___x_1132_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_b_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_tail_1130_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_size_1146_; lean_object* v_buckets_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1190_; 
v_size_1146_ = lean_ctor_get(v_m_1143_, 0);
v_buckets_1147_ = lean_ctor_get(v_m_1143_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_m_1143_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1149_ = v_m_1143_;
v_isShared_1150_ = v_isSharedCheck_1190_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_buckets_1147_);
lean_inc(v_size_1146_);
lean_dec(v_m_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1190_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v_fold_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; lean_object* v_bkt_1164_; uint8_t v___x_1165_; 
v___x_1151_ = lean_array_get_size(v_buckets_1147_);
v___x_1152_ = l_Lean_Expr_hash(v_a_1144_);
v___x_1153_ = 32ULL;
v___x_1154_ = lean_uint64_shift_right(v___x_1152_, v___x_1153_);
v_fold_1155_ = lean_uint64_xor(v___x_1152_, v___x_1154_);
v___x_1156_ = 16ULL;
v___x_1157_ = lean_uint64_shift_right(v_fold_1155_, v___x_1156_);
v___x_1158_ = lean_uint64_xor(v_fold_1155_, v___x_1157_);
v___x_1159_ = lean_uint64_to_usize(v___x_1158_);
v___x_1160_ = lean_usize_of_nat(v___x_1151_);
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_sub(v___x_1160_, v___x_1161_);
v___x_1163_ = lean_usize_land(v___x_1159_, v___x_1162_);
v_bkt_1164_ = lean_array_uget_borrowed(v_buckets_1147_, v___x_1163_);
v___x_1165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1144_, v_bkt_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v_size_x27_1167_; lean_object* v___x_1168_; lean_object* v_buckets_x27_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v_size_x27_1167_ = lean_nat_add(v_size_1146_, v___x_1166_);
lean_dec(v_size_1146_);
lean_inc(v_bkt_1164_);
v___x_1168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1144_);
lean_ctor_set(v___x_1168_, 1, v_b_1145_);
lean_ctor_set(v___x_1168_, 2, v_bkt_1164_);
v_buckets_x27_1169_ = lean_array_uset(v_buckets_1147_, v___x_1163_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(4u);
v___x_1171_ = lean_nat_mul(v_size_x27_1167_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(3u);
v___x_1173_ = lean_nat_div(v___x_1171_, v___x_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_array_get_size(v_buckets_x27_1169_);
v___x_1175_ = lean_nat_dec_le(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
if (v___x_1175_ == 0)
{
lean_object* v_val_1176_; lean_object* v___x_1178_; 
v_val_1176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1169_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_val_1176_);
lean_ctor_set(v___x_1149_, 0, v_size_x27_1167_);
v___x_1178_ = v___x_1149_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_size_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_val_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v___x_1181_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_buckets_x27_1169_);
lean_ctor_set(v___x_1149_, 0, v_size_x27_1167_);
v___x_1181_ = v___x_1149_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_size_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_buckets_x27_1169_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v_buckets_x27_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc(v_bkt_1164_);
v___x_1183_ = lean_box(0);
v_buckets_x27_1184_ = lean_array_uset(v_buckets_1147_, v___x_1163_, v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1144_, v_b_1145_, v_bkt_1164_);
v___x_1186_ = lean_array_uset(v_buckets_x27_1184_, v___x_1163_, v___x_1185_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1186_);
v___x_1188_ = v___x_1149_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_size_1146_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object* v_k_1191_, uint8_t v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v_b_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_box(v___y_1192_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
v___x_1202_ = lean_apply_9(v_k_1191_, v_b_1195_, v___x_1201_, v___y_1193_, v___y_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v___y_66738__boxed_1213_; lean_object* v_res_1214_; 
v___y_66738__boxed_1213_ = lean_unbox(v___y_1204_);
v_res_1214_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1203_, v___y_66738__boxed_1213_, v___y_1205_, v___y_1206_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object* v_name_1215_, uint8_t v_bi_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, uint8_t v_kind_1219_, uint8_t v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(v___y_1220_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1229_, 0, v_k_1218_);
lean_closure_set(v___f_1229_, 1, v___x_1228_);
lean_closure_set(v___f_1229_, 2, v___y_1221_);
lean_closure_set(v___f_1229_, 3, v___y_1222_);
v___x_1230_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1215_, v_bi_1216_, v_type_1217_, v___f_1229_, v_kind_1219_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1230_) == 0)
{
return v___x_1230_;
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object* v_name_1239_, lean_object* v_bi_1240_, lean_object* v_type_1241_, lean_object* v_k_1242_, lean_object* v_kind_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_bi_boxed_1252_; uint8_t v_kind_boxed_1253_; uint8_t v___y_66766__boxed_1254_; lean_object* v_res_1255_; 
v_bi_boxed_1252_ = lean_unbox(v_bi_1240_);
v_kind_boxed_1253_ = lean_unbox(v_kind_1243_);
v___y_66766__boxed_1254_ = lean_unbox(v___y_1244_);
v_res_1255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1239_, v_bi_boxed_1252_, v_type_1241_, v_k_1242_, v_kind_boxed_1253_, v___y_66766__boxed_1254_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_env_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1259_ = lean_st_ref_get(v___y_1257_);
v_env_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1259_);
v___x_1261_ = l_Lean_Meta_isMatcherCore(v_env_1260_, v_declName_1256_);
v___x_1262_ = lean_box(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1264_, v___y_1265_);
lean_dec(v___y_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object* v_msgData_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v_env_1275_; lean_object* v___x_1276_; lean_object* v_mctx_1277_; lean_object* v_lctx_1278_; lean_object* v_options_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1274_ = lean_st_ref_get(v___y_1272_);
v_env_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc_ref(v_env_1275_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_st_ref_get(v___y_1270_);
v_mctx_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_ref(v_mctx_1277_);
lean_dec(v___x_1276_);
v_lctx_1278_ = lean_ctor_get(v___y_1269_, 2);
v_options_1279_ = lean_ctor_get(v___y_1271_, 2);
lean_inc_ref(v_options_1279_);
lean_inc_ref(v_lctx_1278_);
v___x_1280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1280_, 0, v_env_1275_);
lean_ctor_set(v___x_1280_, 1, v_mctx_1277_);
lean_ctor_set(v___x_1280_, 2, v_lctx_1278_);
lean_ctor_set(v___x_1280_, 3, v_options_1279_);
v___x_1281_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_msgData_1268_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object* v_msgData_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1290_; double v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_float_of_nat(v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_cls_1295_, lean_object* v_msg_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_ref_1302_; lean_object* v___x_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1348_; 
v_ref_1302_ = lean_ctor_get(v___y_1299_, 5);
v___x_1303_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1348_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1348_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v_traceState_1309_; lean_object* v_env_1310_; lean_object* v_nextMacroScope_1311_; lean_object* v_ngen_1312_; lean_object* v_auxDeclNGen_1313_; lean_object* v_cache_1314_; lean_object* v_messages_1315_; lean_object* v_infoState_1316_; lean_object* v_snapshotTasks_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1347_; 
v___x_1308_ = lean_st_ref_take(v___y_1300_);
v_traceState_1309_ = lean_ctor_get(v___x_1308_, 4);
v_env_1310_ = lean_ctor_get(v___x_1308_, 0);
v_nextMacroScope_1311_ = lean_ctor_get(v___x_1308_, 1);
v_ngen_1312_ = lean_ctor_get(v___x_1308_, 2);
v_auxDeclNGen_1313_ = lean_ctor_get(v___x_1308_, 3);
v_cache_1314_ = lean_ctor_get(v___x_1308_, 5);
v_messages_1315_ = lean_ctor_get(v___x_1308_, 6);
v_infoState_1316_ = lean_ctor_get(v___x_1308_, 7);
v_snapshotTasks_1317_ = lean_ctor_get(v___x_1308_, 8);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1347_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_snapshotTasks_1317_);
lean_inc(v_infoState_1316_);
lean_inc(v_messages_1315_);
lean_inc(v_cache_1314_);
lean_inc(v_traceState_1309_);
lean_inc(v_auxDeclNGen_1313_);
lean_inc(v_ngen_1312_);
lean_inc(v_nextMacroScope_1311_);
lean_inc(v_env_1310_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1347_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
uint64_t v_tid_1321_; lean_object* v_traces_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1346_; 
v_tid_1321_ = lean_ctor_get_uint64(v_traceState_1309_, sizeof(void*)*1);
v_traces_1322_ = lean_ctor_get(v_traceState_1309_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_traceState_1309_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1324_ = v_traceState_1309_;
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_traces_1322_);
lean_dec(v_traceState_1309_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; double v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1328_ = 0;
v___x_1329_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1330_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1330_, 0, v_cls_1295_);
lean_ctor_set(v___x_1330_, 1, v___x_1326_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_ctor_set_float(v___x_1330_, sizeof(void*)*3, v___x_1327_);
lean_ctor_set_float(v___x_1330_, sizeof(void*)*3 + 8, v___x_1327_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*3 + 16, v___x_1328_);
v___x_1331_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1332_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v_a_1304_);
lean_ctor_set(v___x_1332_, 2, v___x_1331_);
lean_inc(v_ref_1302_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_ref_1302_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_PersistentArray_push___redArg(v_traces_1322_, v___x_1333_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1334_);
v___x_1336_ = v___x_1324_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1334_);
lean_ctor_set_uint64(v_reuseFailAlloc_1345_, sizeof(void*)*1, v_tid_1321_);
v___x_1336_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 4, v___x_1336_);
v___x_1338_ = v___x_1319_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_env_1310_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_nextMacroScope_1311_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_ngen_1312_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_auxDeclNGen_1313_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 5, v_cache_1314_);
lean_ctor_set(v_reuseFailAlloc_1344_, 6, v_messages_1315_);
lean_ctor_set(v_reuseFailAlloc_1344_, 7, v_infoState_1316_);
lean_ctor_set(v_reuseFailAlloc_1344_, 8, v_snapshotTasks_1317_);
v___x_1338_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_st_ref_set(v___y_1300_, v___x_1338_);
v___x_1340_ = lean_box(0);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1340_);
v___x_1342_ = v___x_1306_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1349_, lean_object* v_msg_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1349_, v_msg_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
else
{
lean_object* v_key_1360_; lean_object* v_value_1361_; lean_object* v_tail_1362_; uint8_t v___x_1363_; 
v_key_1360_ = lean_ctor_get(v_x_1358_, 0);
v_value_1361_ = lean_ctor_get(v_x_1358_, 1);
v_tail_1362_ = lean_ctor_get(v_x_1358_, 2);
v___x_1363_ = lean_expr_eqv(v_key_1360_, v_a_1357_);
if (v___x_1363_ == 0)
{
v_x_1358_ = v_tail_1362_;
goto _start;
}
else
{
lean_object* v___x_1365_; 
lean_inc(v_value_1361_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_value_1361_);
return v___x_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1366_, v_x_1367_);
lean_dec(v_x_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_buckets_1371_; lean_object* v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; uint64_t v___x_1375_; uint64_t v_fold_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_buckets_1371_ = lean_ctor_get(v_m_1369_, 1);
v___x_1372_ = lean_array_get_size(v_buckets_1371_);
v___x_1373_ = l_Lean_Expr_hash(v_a_1370_);
v___x_1374_ = 32ULL;
v___x_1375_ = lean_uint64_shift_right(v___x_1373_, v___x_1374_);
v_fold_1376_ = lean_uint64_xor(v___x_1373_, v___x_1375_);
v___x_1377_ = 16ULL;
v___x_1378_ = lean_uint64_shift_right(v_fold_1376_, v___x_1377_);
v___x_1379_ = lean_uint64_xor(v_fold_1376_, v___x_1378_);
v___x_1380_ = lean_uint64_to_usize(v___x_1379_);
v___x_1381_ = lean_usize_of_nat(v___x_1372_);
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_sub(v___x_1381_, v___x_1382_);
v___x_1384_ = lean_usize_land(v___x_1380_, v___x_1383_);
v___x_1385_ = lean_array_uget_borrowed(v_buckets_1371_, v___x_1384_);
v___x_1386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1370_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1387_, v_a_1388_);
lean_dec_ref(v_a_1388_);
lean_dec_ref(v_m_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1390_, lean_object* v_type_1391_, lean_object* v_val_1392_, lean_object* v_k_1393_, uint8_t v_nondep_1394_, uint8_t v_kind_1395_, uint8_t v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(v___y_1396_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___f_1405_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1405_, 0, v_k_1393_);
lean_closure_set(v___f_1405_, 1, v___x_1404_);
lean_closure_set(v___f_1405_, 2, v___y_1397_);
lean_closure_set(v___f_1405_, 3, v___y_1398_);
v___x_1406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1390_, v_type_1391_, v_val_1392_, v___f_1405_, v_nondep_1394_, v_kind_1395_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1406_) == 0)
{
return v___x_1406_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1415_, lean_object* v_type_1416_, lean_object* v_val_1417_, lean_object* v_k_1418_, lean_object* v_nondep_1419_, lean_object* v_kind_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_nondep_boxed_1429_; uint8_t v_kind_boxed_1430_; uint8_t v___y_67001__boxed_1431_; lean_object* v_res_1432_; 
v_nondep_boxed_1429_ = lean_unbox(v_nondep_1419_);
v_kind_boxed_1430_ = lean_unbox(v_kind_1420_);
v___y_67001__boxed_1431_ = lean_unbox(v___y_1421_);
v_res_1432_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1415_, v_type_1416_, v_val_1417_, v_k_1418_, v_nondep_boxed_1429_, v_kind_boxed_1430_, v___y_67001__boxed_1431_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = l_Lean_instInhabitedExpr;
v___x_1435_ = lean_panic_fn_borrowed(v___x_1434_, v_msg_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1438_, lean_object* v_body_1439_, lean_object* v_x_1440_, uint8_t v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_array_push(v_fvars_1438_, v_x_1440_);
v___x_1450_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1449_, v_body_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1451_, lean_object* v_body_1452_, lean_object* v_x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v___y_67164__boxed_1462_; lean_object* v_res_1463_; 
v___y_67164__boxed_1462_ = lean_unbox(v___y_1454_);
v_res_1463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1451_, v_body_1452_, v_x_1453_, v___y_67164__boxed_1462_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1464_, lean_object* v_e_1465_, uint8_t v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
if (lean_obj_tag(v_e_1465_) == 6)
{
lean_object* v_binderName_1474_; lean_object* v_binderType_1475_; lean_object* v_body_1476_; uint8_t v_binderInfo_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_binderName_1474_ = lean_ctor_get(v_e_1465_, 0);
lean_inc(v_binderName_1474_);
v_binderType_1475_ = lean_ctor_get(v_e_1465_, 1);
lean_inc_ref(v_binderType_1475_);
v_body_1476_ = lean_ctor_get(v_e_1465_, 2);
lean_inc_ref(v_body_1476_);
v_binderInfo_1477_ = lean_ctor_get_uint8(v_e_1465_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1465_, 3);
v___x_1478_ = lean_expr_instantiate_rev(v_binderType_1475_, v_fvars_1464_);
lean_dec_ref(v_binderType_1475_);
v___x_1479_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1478_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___f_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___f_1481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1481_, 0, v_fvars_1464_);
lean_closure_set(v___f_1481_, 1, v_body_1476_);
v___x_1482_ = 0;
v___x_1483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1474_, v_binderInfo_1477_, v_a_1480_, v___f_1481_, v___x_1482_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1483_;
}
else
{
lean_dec_ref(v_body_1476_);
lean_dec(v_binderName_1474_);
lean_dec_ref(v_fvars_1464_);
return v___x_1479_;
}
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_expr_instantiate_rev(v_e_1465_, v_fvars_1464_);
lean_dec_ref(v_e_1465_);
v___x_1485_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1484_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; uint8_t v___x_1487_; uint8_t v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = 0;
v___x_1488_ = 1;
v___x_1489_ = 1;
v___x_1490_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1464_, v_a_1486_, v___x_1487_, v___x_1488_, v___x_1487_, v___x_1488_, v___x_1489_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec_ref(v_fvars_1464_);
return v___x_1490_;
}
else
{
lean_dec_ref(v_fvars_1464_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1491_, uint8_t v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
if (v_a_1492_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1501_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1500_, v_e_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1503_ = l_Lean_Meta_Sym_etaReduce(v_e_1491_);
lean_dec_ref(v_e_1491_);
v___x_1504_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1502_, v___x_1503_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1505_, lean_object* v_body_1506_, lean_object* v_x_1507_, uint8_t v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_array_push(v_fvars_1505_, v_x_1507_);
v___x_1517_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1516_, v_body_1506_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1518_, lean_object* v_body_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v___y_67175__boxed_1529_; lean_object* v_res_1530_; 
v___y_67175__boxed_1529_ = lean_unbox(v___y_1521_);
v_res_1530_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1518_, v_body_1519_, v_x_1520_, v___y_67175__boxed_1529_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1531_, lean_object* v_e_1532_, uint8_t v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
if (lean_obj_tag(v_e_1532_) == 8)
{
lean_object* v_declName_1541_; lean_object* v_type_1542_; lean_object* v_value_1543_; lean_object* v_body_1544_; uint8_t v_nondep_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_declName_1541_ = lean_ctor_get(v_e_1532_, 0);
lean_inc(v_declName_1541_);
v_type_1542_ = lean_ctor_get(v_e_1532_, 1);
lean_inc_ref(v_type_1542_);
v_value_1543_ = lean_ctor_get(v_e_1532_, 2);
lean_inc_ref(v_value_1543_);
v_body_1544_ = lean_ctor_get(v_e_1532_, 3);
lean_inc_ref(v_body_1544_);
v_nondep_1545_ = lean_ctor_get_uint8(v_e_1532_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1532_, 4);
v___x_1546_ = lean_expr_instantiate_rev(v_type_1542_, v_fvars_1531_);
lean_dec_ref(v_type_1542_);
v___x_1547_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1546_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = lean_expr_instantiate_rev(v_value_1543_, v_fvars_1531_);
lean_dec_ref(v_value_1543_);
v___x_1550_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1549_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___f_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___f_1552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1552_, 0, v_fvars_1531_);
lean_closure_set(v___f_1552_, 1, v_body_1544_);
v___x_1553_ = 0;
v___x_1554_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1541_, v_a_1548_, v_a_1551_, v___f_1552_, v_nondep_1545_, v___x_1553_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
return v___x_1554_;
}
else
{
lean_dec(v_a_1548_);
lean_dec_ref(v_body_1544_);
lean_dec(v_declName_1541_);
lean_dec_ref(v_fvars_1531_);
return v___x_1550_;
}
}
else
{
lean_dec_ref(v_body_1544_);
lean_dec_ref(v_value_1543_);
lean_dec(v_declName_1541_);
lean_dec_ref(v_fvars_1531_);
return v___x_1547_;
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_expr_instantiate_rev(v_e_1532_, v_fvars_1531_);
lean_dec_ref(v_e_1532_);
v___x_1556_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1555_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; uint8_t v___x_1560_; lean_object* v___x_1561_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = 1;
v___x_1559_ = 0;
v___x_1560_ = 1;
v___x_1561_ = l_Lean_Meta_mkLetFVars(v_fvars_1531_, v_a_1557_, v___x_1558_, v___x_1559_, v___x_1560_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec_ref(v_fvars_1531_);
return v___x_1561_;
}
else
{
lean_dec_ref(v_fvars_1531_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1562_, uint8_t v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
if (v_a_1563_ == 0)
{
uint8_t v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = 1;
v___x_1572_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1562_, v___x_1571_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1574_, uint8_t v_report_1575_, uint8_t v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
lean_inc(v_a_1580_);
lean_inc_ref(v_a_1579_);
lean_inc_ref(v_e_1574_);
v___x_1584_ = lean_infer_type(v_e_1574_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_n(v_a_1585_, 2);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l_Lean_Meta_isProp(v_a_1585_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1599_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1599_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1599_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
if (v_a_1576_ == 0)
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_unbox(v_a_1587_);
lean_dec(v_a_1587_);
if (v___x_1595_ == 0)
{
lean_del_object(v___x_1589_);
goto v___jp_1591_;
}
else
{
lean_object* v___x_1597_; 
lean_dec(v_a_1585_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_e_1574_);
v___x_1597_ = v___x_1589_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_e_1574_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_del_object(v___x_1589_);
lean_dec(v_a_1587_);
goto v___jp_1591_;
}
v___jp_1591_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1585_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1574_, v_a_1593_, v_report_1575_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1594_;
}
else
{
lean_dec_ref(v_e_1574_);
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1585_);
lean_dec_ref(v_e_1574_);
v_a_1600_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1586_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1586_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_dec_ref(v_e_1574_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1608_, uint8_t v_report_1609_, uint8_t v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
if (v_a_1610_ == 0)
{
lean_object* v___x_1618_; lean_object* v_canon_1619_; lean_object* v_cache_1620_; lean_object* v___x_1621_; 
v___x_1618_ = lean_st_ref_get(v_a_1612_);
v_canon_1619_ = lean_ctor_get(v___x_1618_, 9);
lean_inc_ref(v_canon_1619_);
lean_dec(v___x_1618_);
v_cache_1620_ = lean_ctor_get(v_canon_1619_, 0);
lean_inc_ref(v_cache_1620_);
lean_dec_ref(v_canon_1619_);
v___x_1621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1620_, v_e_1608_);
lean_dec_ref(v_cache_1620_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_e_1608_);
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 0);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_val_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___x_1621_);
lean_inc_ref(v_e_1608_);
v___x_1630_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1608_, v_report_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1669_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1669_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1669_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v_canon_1636_; lean_object* v_share_1637_; lean_object* v_maxFVar_1638_; lean_object* v_proofInstInfo_1639_; lean_object* v_inferType_1640_; lean_object* v_getLevel_1641_; lean_object* v_congrInfo_1642_; lean_object* v_defEqI_1643_; lean_object* v_extensions_1644_; lean_object* v_issues_1645_; lean_object* v_instanceOverrides_1646_; uint8_t v_debug_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1668_; 
v___x_1635_ = lean_st_ref_take(v_a_1612_);
v_canon_1636_ = lean_ctor_get(v___x_1635_, 9);
v_share_1637_ = lean_ctor_get(v___x_1635_, 0);
v_maxFVar_1638_ = lean_ctor_get(v___x_1635_, 1);
v_proofInstInfo_1639_ = lean_ctor_get(v___x_1635_, 2);
v_inferType_1640_ = lean_ctor_get(v___x_1635_, 3);
v_getLevel_1641_ = lean_ctor_get(v___x_1635_, 4);
v_congrInfo_1642_ = lean_ctor_get(v___x_1635_, 5);
v_defEqI_1643_ = lean_ctor_get(v___x_1635_, 6);
v_extensions_1644_ = lean_ctor_get(v___x_1635_, 7);
v_issues_1645_ = lean_ctor_get(v___x_1635_, 8);
v_instanceOverrides_1646_ = lean_ctor_get(v___x_1635_, 10);
v_debug_1647_ = lean_ctor_get_uint8(v___x_1635_, sizeof(void*)*11);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1649_ = v___x_1635_;
v_isShared_1650_ = v_isSharedCheck_1668_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_instanceOverrides_1646_);
lean_inc(v_canon_1636_);
lean_inc(v_issues_1645_);
lean_inc(v_extensions_1644_);
lean_inc(v_defEqI_1643_);
lean_inc(v_congrInfo_1642_);
lean_inc(v_getLevel_1641_);
lean_inc(v_inferType_1640_);
lean_inc(v_proofInstInfo_1639_);
lean_inc(v_maxFVar_1638_);
lean_inc(v_share_1637_);
lean_dec(v___x_1635_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1668_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_cache_1651_; lean_object* v_cacheInType_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1667_; 
v_cache_1651_ = lean_ctor_get(v_canon_1636_, 0);
v_cacheInType_1652_ = lean_ctor_get(v_canon_1636_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_canon_1636_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1654_ = v_canon_1636_;
v_isShared_1655_ = v_isSharedCheck_1667_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_cacheInType_1652_);
lean_inc(v_cache_1651_);
lean_dec(v_canon_1636_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1667_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_inc(v_a_1631_);
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1651_, v_e_1608_, v_a_1631_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1656_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_cacheInType_1652_);
v___x_1658_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 9, v___x_1658_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_share_1637_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_maxFVar_1638_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_proofInstInfo_1639_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_inferType_1640_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_getLevel_1641_);
lean_ctor_set(v_reuseFailAlloc_1665_, 5, v_congrInfo_1642_);
lean_ctor_set(v_reuseFailAlloc_1665_, 6, v_defEqI_1643_);
lean_ctor_set(v_reuseFailAlloc_1665_, 7, v_extensions_1644_);
lean_ctor_set(v_reuseFailAlloc_1665_, 8, v_issues_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 9, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 10, v_instanceOverrides_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1665_, sizeof(void*)*11, v_debug_1647_);
v___x_1660_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_st_ref_set(v_a_1612_, v___x_1660_);
if (v_isShared_1634_ == 0)
{
v___x_1663_ = v___x_1633_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1631_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1608_);
return v___x_1630_;
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v_canon_1671_; lean_object* v_cacheInType_1672_; lean_object* v___x_1673_; 
v___x_1670_ = lean_st_ref_get(v_a_1612_);
v_canon_1671_ = lean_ctor_get(v___x_1670_, 9);
lean_inc_ref(v_canon_1671_);
lean_dec(v___x_1670_);
v_cacheInType_1672_ = lean_ctor_get(v_canon_1671_, 1);
lean_inc_ref(v_cacheInType_1672_);
lean_dec_ref(v_canon_1671_);
v___x_1673_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1672_, v_e_1608_);
lean_dec_ref(v_cacheInType_1672_);
if (lean_obj_tag(v___x_1673_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_e_1608_);
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_val_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 0);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_val_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v___x_1682_; 
lean_dec(v___x_1673_);
lean_inc_ref(v_e_1608_);
v___x_1682_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1608_, v_report_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1721_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1721_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1721_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v_canon_1688_; lean_object* v_share_1689_; lean_object* v_maxFVar_1690_; lean_object* v_proofInstInfo_1691_; lean_object* v_inferType_1692_; lean_object* v_getLevel_1693_; lean_object* v_congrInfo_1694_; lean_object* v_defEqI_1695_; lean_object* v_extensions_1696_; lean_object* v_issues_1697_; lean_object* v_instanceOverrides_1698_; uint8_t v_debug_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1720_; 
v___x_1687_ = lean_st_ref_take(v_a_1612_);
v_canon_1688_ = lean_ctor_get(v___x_1687_, 9);
v_share_1689_ = lean_ctor_get(v___x_1687_, 0);
v_maxFVar_1690_ = lean_ctor_get(v___x_1687_, 1);
v_proofInstInfo_1691_ = lean_ctor_get(v___x_1687_, 2);
v_inferType_1692_ = lean_ctor_get(v___x_1687_, 3);
v_getLevel_1693_ = lean_ctor_get(v___x_1687_, 4);
v_congrInfo_1694_ = lean_ctor_get(v___x_1687_, 5);
v_defEqI_1695_ = lean_ctor_get(v___x_1687_, 6);
v_extensions_1696_ = lean_ctor_get(v___x_1687_, 7);
v_issues_1697_ = lean_ctor_get(v___x_1687_, 8);
v_instanceOverrides_1698_ = lean_ctor_get(v___x_1687_, 10);
v_debug_1699_ = lean_ctor_get_uint8(v___x_1687_, sizeof(void*)*11);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1701_ = v___x_1687_;
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_instanceOverrides_1698_);
lean_inc(v_canon_1688_);
lean_inc(v_issues_1697_);
lean_inc(v_extensions_1696_);
lean_inc(v_defEqI_1695_);
lean_inc(v_congrInfo_1694_);
lean_inc(v_getLevel_1693_);
lean_inc(v_inferType_1692_);
lean_inc(v_proofInstInfo_1691_);
lean_inc(v_maxFVar_1690_);
lean_inc(v_share_1689_);
lean_dec(v___x_1687_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_cache_1703_; lean_object* v_cacheInType_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1719_; 
v_cache_1703_ = lean_ctor_get(v_canon_1688_, 0);
v_cacheInType_1704_ = lean_ctor_get(v_canon_1688_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_canon_1688_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1706_ = v_canon_1688_;
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_cacheInType_1704_);
lean_inc(v_cache_1703_);
lean_dec(v_canon_1688_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_inc(v_a_1683_);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1704_, v_e_1608_, v_a_1683_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v___x_1708_);
v___x_1710_ = v___x_1706_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_cache_1703_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 9, v___x_1710_);
v___x_1712_ = v___x_1701_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_share_1689_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_maxFVar_1690_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_proofInstInfo_1691_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_inferType_1692_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_getLevel_1693_);
lean_ctor_set(v_reuseFailAlloc_1717_, 5, v_congrInfo_1694_);
lean_ctor_set(v_reuseFailAlloc_1717_, 6, v_defEqI_1695_);
lean_ctor_set(v_reuseFailAlloc_1717_, 7, v_extensions_1696_);
lean_ctor_set(v_reuseFailAlloc_1717_, 8, v_issues_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 9, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1717_, 10, v_instanceOverrides_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1717_, sizeof(void*)*11, v_debug_1699_);
v___x_1712_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_st_ref_set(v_a_1612_, v___x_1712_);
if (v_isShared_1686_ == 0)
{
v___x_1715_ = v___x_1685_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1683_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1608_);
return v___x_1682_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(0);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1738_ = l_Lean_mkConst(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1739_, lean_object* v_prop_1740_, lean_object* v_inst_1741_, lean_object* v_e_1742_, uint8_t v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; 
lean_inc_ref(v_prop_1740_);
v___x_1751_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1740_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1791_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___y_1757_; uint8_t v___y_1758_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1752_);
v___x_1767_ = l_Lean_Expr_app___override(v___x_1766_, v_a_1752_);
if (v_a_1743_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1767_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___y_1771_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
if (lean_obj_tag(v_a_1769_) == 0)
{
lean_inc_ref(v_inst_1741_);
v___y_1771_ = v_inst_1741_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v_a_1769_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v_a_1769_, 1);
v___y_1771_ = v_val_1780_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
lean_inc_ref(v_inst_1741_);
v___x_1772_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1741_, v___y_1771_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; size_t v___x_1774_; size_t v___x_1775_; uint8_t v___x_1776_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = lean_ptr_addr(v_prop_1740_);
lean_dec_ref(v_prop_1740_);
v___x_1775_ = lean_ptr_addr(v_a_1752_);
v___x_1776_ = lean_usize_dec_eq(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v_inst_1741_);
v___y_1757_ = v_a_1773_;
v___y_1758_ = v___x_1776_;
goto v___jp_1756_;
}
else
{
size_t v___x_1777_; size_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = lean_ptr_addr(v_inst_1741_);
lean_dec_ref(v_inst_1741_);
v___x_1778_ = lean_ptr_addr(v_a_1773_);
v___x_1779_ = lean_usize_dec_eq(v___x_1777_, v___x_1778_);
v___y_1757_ = v_a_1773_;
v___y_1758_ = v___x_1779_;
goto v___jp_1756_;
}
}
else
{
lean_del_object(v___x_1754_);
lean_dec(v_a_1752_);
lean_dec_ref(v_e_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_prop_1740_);
lean_dec_ref(v_g_1739_);
return v___x_1772_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1754_);
lean_dec(v_a_1752_);
lean_dec_ref(v_e_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_prop_1740_);
lean_dec_ref(v_g_1739_);
v_a_1781_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1768_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1768_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
uint8_t v___x_1789_; lean_object* v___x_1790_; 
lean_del_object(v___x_1754_);
lean_dec(v_a_1752_);
lean_dec_ref(v_e_1742_);
lean_dec_ref(v_prop_1740_);
lean_dec_ref(v_g_1739_);
v___x_1789_ = 0;
v___x_1790_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1741_, v___x_1767_, v___x_1789_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1790_;
}
v___jp_1756_:
{
if (v___y_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec_ref(v_e_1742_);
v___x_1759_ = l_Lean_mkAppB(v_g_1739_, v_a_1752_, v___y_1757_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1759_);
v___x_1761_ = v___x_1754_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
else
{
lean_object* v___x_1764_; 
lean_dec_ref(v___y_1757_);
lean_dec(v_a_1752_);
lean_dec_ref(v_g_1739_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v_e_1742_);
v___x_1764_ = v___x_1754_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_e_1742_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_prop_1740_);
lean_dec_ref(v_g_1739_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1792_, lean_object* v_prop_1793_, lean_object* v_h_1794_, lean_object* v_e_1795_, uint8_t v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
if (v_a_1796_ == 0)
{
lean_object* v___x_1804_; lean_object* v_canon_1805_; lean_object* v_cache_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_st_ref_get(v_a_1798_);
v_canon_1805_ = lean_ctor_get(v___x_1804_, 9);
lean_inc_ref(v_canon_1805_);
lean_dec(v___x_1804_);
v_cache_1806_ = lean_ctor_get(v_canon_1805_, 0);
lean_inc_ref(v_cache_1806_);
lean_dec_ref(v_canon_1805_);
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1806_, v_e_1795_);
lean_dec_ref(v_cache_1806_);
if (lean_obj_tag(v___x_1807_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_e_1795_);
lean_dec_ref(v_h_1794_);
lean_dec_ref(v_prop_1793_);
lean_dec_ref(v_g_1792_);
v_val_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_val_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 0);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_val_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v___x_1807_);
lean_inc_ref(v_e_1795_);
v___x_1816_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1792_, v_prop_1793_, v_h_1794_, v_e_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1855_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1855_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1855_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v_canon_1822_; lean_object* v_share_1823_; lean_object* v_maxFVar_1824_; lean_object* v_proofInstInfo_1825_; lean_object* v_inferType_1826_; lean_object* v_getLevel_1827_; lean_object* v_congrInfo_1828_; lean_object* v_defEqI_1829_; lean_object* v_extensions_1830_; lean_object* v_issues_1831_; lean_object* v_instanceOverrides_1832_; uint8_t v_debug_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1854_; 
v___x_1821_ = lean_st_ref_take(v_a_1798_);
v_canon_1822_ = lean_ctor_get(v___x_1821_, 9);
v_share_1823_ = lean_ctor_get(v___x_1821_, 0);
v_maxFVar_1824_ = lean_ctor_get(v___x_1821_, 1);
v_proofInstInfo_1825_ = lean_ctor_get(v___x_1821_, 2);
v_inferType_1826_ = lean_ctor_get(v___x_1821_, 3);
v_getLevel_1827_ = lean_ctor_get(v___x_1821_, 4);
v_congrInfo_1828_ = lean_ctor_get(v___x_1821_, 5);
v_defEqI_1829_ = lean_ctor_get(v___x_1821_, 6);
v_extensions_1830_ = lean_ctor_get(v___x_1821_, 7);
v_issues_1831_ = lean_ctor_get(v___x_1821_, 8);
v_instanceOverrides_1832_ = lean_ctor_get(v___x_1821_, 10);
v_debug_1833_ = lean_ctor_get_uint8(v___x_1821_, sizeof(void*)*11);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1835_ = v___x_1821_;
v_isShared_1836_ = v_isSharedCheck_1854_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_instanceOverrides_1832_);
lean_inc(v_canon_1822_);
lean_inc(v_issues_1831_);
lean_inc(v_extensions_1830_);
lean_inc(v_defEqI_1829_);
lean_inc(v_congrInfo_1828_);
lean_inc(v_getLevel_1827_);
lean_inc(v_inferType_1826_);
lean_inc(v_proofInstInfo_1825_);
lean_inc(v_maxFVar_1824_);
lean_inc(v_share_1823_);
lean_dec(v___x_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1854_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_cache_1837_; lean_object* v_cacheInType_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1853_; 
v_cache_1837_ = lean_ctor_get(v_canon_1822_, 0);
v_cacheInType_1838_ = lean_ctor_get(v_canon_1822_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_canon_1822_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1840_ = v_canon_1822_;
v_isShared_1841_ = v_isSharedCheck_1853_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_cacheInType_1838_);
lean_inc(v_cache_1837_);
lean_dec(v_canon_1822_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1853_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_inc(v_a_1817_);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1837_, v_e_1795_, v_a_1817_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_cacheInType_1838_);
v___x_1844_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 9, v___x_1844_);
v___x_1846_ = v___x_1835_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_share_1823_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_maxFVar_1824_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_proofInstInfo_1825_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_inferType_1826_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_getLevel_1827_);
lean_ctor_set(v_reuseFailAlloc_1851_, 5, v_congrInfo_1828_);
lean_ctor_set(v_reuseFailAlloc_1851_, 6, v_defEqI_1829_);
lean_ctor_set(v_reuseFailAlloc_1851_, 7, v_extensions_1830_);
lean_ctor_set(v_reuseFailAlloc_1851_, 8, v_issues_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 9, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1851_, 10, v_instanceOverrides_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*11, v_debug_1833_);
v___x_1846_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_set(v_a_1798_, v___x_1846_);
if (v_isShared_1820_ == 0)
{
v___x_1849_ = v___x_1819_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1817_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1795_);
return v___x_1816_;
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v_canon_1857_; lean_object* v_cacheInType_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_st_ref_get(v_a_1798_);
v_canon_1857_ = lean_ctor_get(v___x_1856_, 9);
lean_inc_ref(v_canon_1857_);
lean_dec(v___x_1856_);
v_cacheInType_1858_ = lean_ctor_get(v_canon_1857_, 1);
lean_inc_ref(v_cacheInType_1858_);
lean_dec_ref(v_canon_1857_);
v___x_1859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1858_, v_e_1795_);
lean_dec_ref(v_cacheInType_1858_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_e_1795_);
lean_dec_ref(v_h_1794_);
lean_dec_ref(v_prop_1793_);
lean_dec_ref(v_g_1792_);
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_val_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_val_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v___x_1868_; 
lean_dec(v___x_1859_);
lean_inc_ref(v_e_1795_);
v___x_1868_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1792_, v_prop_1793_, v_h_1794_, v_e_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1907_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1907_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1907_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v_canon_1874_; lean_object* v_share_1875_; lean_object* v_maxFVar_1876_; lean_object* v_proofInstInfo_1877_; lean_object* v_inferType_1878_; lean_object* v_getLevel_1879_; lean_object* v_congrInfo_1880_; lean_object* v_defEqI_1881_; lean_object* v_extensions_1882_; lean_object* v_issues_1883_; lean_object* v_instanceOverrides_1884_; uint8_t v_debug_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1906_; 
v___x_1873_ = lean_st_ref_take(v_a_1798_);
v_canon_1874_ = lean_ctor_get(v___x_1873_, 9);
v_share_1875_ = lean_ctor_get(v___x_1873_, 0);
v_maxFVar_1876_ = lean_ctor_get(v___x_1873_, 1);
v_proofInstInfo_1877_ = lean_ctor_get(v___x_1873_, 2);
v_inferType_1878_ = lean_ctor_get(v___x_1873_, 3);
v_getLevel_1879_ = lean_ctor_get(v___x_1873_, 4);
v_congrInfo_1880_ = lean_ctor_get(v___x_1873_, 5);
v_defEqI_1881_ = lean_ctor_get(v___x_1873_, 6);
v_extensions_1882_ = lean_ctor_get(v___x_1873_, 7);
v_issues_1883_ = lean_ctor_get(v___x_1873_, 8);
v_instanceOverrides_1884_ = lean_ctor_get(v___x_1873_, 10);
v_debug_1885_ = lean_ctor_get_uint8(v___x_1873_, sizeof(void*)*11);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1887_ = v___x_1873_;
v_isShared_1888_ = v_isSharedCheck_1906_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_instanceOverrides_1884_);
lean_inc(v_canon_1874_);
lean_inc(v_issues_1883_);
lean_inc(v_extensions_1882_);
lean_inc(v_defEqI_1881_);
lean_inc(v_congrInfo_1880_);
lean_inc(v_getLevel_1879_);
lean_inc(v_inferType_1878_);
lean_inc(v_proofInstInfo_1877_);
lean_inc(v_maxFVar_1876_);
lean_inc(v_share_1875_);
lean_dec(v___x_1873_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1906_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_cache_1889_; lean_object* v_cacheInType_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1905_; 
v_cache_1889_ = lean_ctor_get(v_canon_1874_, 0);
v_cacheInType_1890_ = lean_ctor_get(v_canon_1874_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_canon_1874_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1892_ = v_canon_1874_;
v_isShared_1893_ = v_isSharedCheck_1905_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_cacheInType_1890_);
lean_inc(v_cache_1889_);
lean_dec(v_canon_1874_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1905_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_inc(v_a_1869_);
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1890_, v_e_1795_, v_a_1869_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_cache_1889_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 9, v___x_1896_);
v___x_1898_ = v___x_1887_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_share_1875_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_maxFVar_1876_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_proofInstInfo_1877_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_inferType_1878_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_getLevel_1879_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v_congrInfo_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 6, v_defEqI_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 7, v_extensions_1882_);
lean_ctor_set(v_reuseFailAlloc_1903_, 8, v_issues_1883_);
lean_ctor_set(v_reuseFailAlloc_1903_, 9, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 10, v_instanceOverrides_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1903_, sizeof(void*)*11, v_debug_1885_);
v___x_1898_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_st_ref_set(v_a_1798_, v___x_1898_);
if (v_isShared_1872_ == 0)
{
v___x_1901_ = v___x_1871_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1869_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1795_);
return v___x_1868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1908_, lean_object* v_prop_1909_, lean_object* v_h_1910_, lean_object* v_e_1911_, uint8_t v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_a_1921_; lean_object* v___y_1955_; 
if (v_a_1912_ == 0)
{
lean_object* v___x_1995_; lean_object* v_canon_1996_; lean_object* v_cache_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_st_ref_get(v_a_1914_);
v_canon_1996_ = lean_ctor_get(v___x_1995_, 9);
lean_inc_ref(v_canon_1996_);
lean_dec(v___x_1995_);
v_cache_1997_ = lean_ctor_get(v_canon_1996_, 0);
lean_inc_ref(v_cache_1997_);
lean_dec_ref(v_canon_1996_);
v___x_1998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1997_, v_e_1911_);
lean_dec_ref(v_cache_1997_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_e_1911_);
lean_dec_ref(v_h_1910_);
lean_dec_ref(v_prop_1909_);
lean_dec_ref(v_g_1908_);
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 0);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_val_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v___x_1998_);
lean_inc_ref(v_prop_1909_);
v___x_2007_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1909_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc_n(v_a_2008_, 2);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2008_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v___y_2016_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
if (lean_obj_tag(v_a_2010_) == 0)
{
lean_inc_ref(v_h_1910_);
v___y_2016_ = v_h_1910_;
goto v___jp_2015_;
}
else
{
lean_object* v_val_2023_; 
v_val_2023_ = lean_ctor_get(v_a_2010_, 0);
lean_inc(v_val_2023_);
lean_dec_ref_known(v_a_2010_, 1);
v___y_2016_ = v_val_2023_;
goto v___jp_2015_;
}
v___jp_2011_:
{
if (v___y_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_mkAppB(v_g_1908_, v_a_2008_, v___y_2012_);
v_a_1921_ = v___x_2014_;
goto v___jp_1920_;
}
else
{
lean_dec_ref(v___y_2012_);
lean_dec(v_a_2008_);
lean_dec_ref(v_g_1908_);
lean_inc_ref(v_e_1911_);
v_a_1921_ = v_e_1911_;
goto v___jp_1920_;
}
}
v___jp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; uint8_t v___x_2019_; 
v___x_2017_ = lean_ptr_addr(v_prop_1909_);
lean_dec_ref(v_prop_1909_);
v___x_2018_ = lean_ptr_addr(v_a_2008_);
v___x_2019_ = lean_usize_dec_eq(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_dec_ref(v_h_1910_);
v___y_2012_ = v___y_2016_;
v___y_2013_ = v___x_2019_;
goto v___jp_2011_;
}
else
{
size_t v___x_2020_; size_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = lean_ptr_addr(v_h_1910_);
lean_dec_ref(v_h_1910_);
v___x_2021_ = lean_ptr_addr(v___y_2016_);
v___x_2022_ = lean_usize_dec_eq(v___x_2020_, v___x_2021_);
v___y_2012_ = v___y_2016_;
v___y_2013_ = v___x_2022_;
goto v___jp_2011_;
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_2008_);
lean_dec_ref(v_e_1911_);
lean_dec_ref(v_h_1910_);
lean_dec_ref(v_prop_1909_);
lean_dec_ref(v_g_1908_);
v_a_2024_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2009_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2009_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_dec_ref(v_h_1910_);
lean_dec_ref(v_prop_1909_);
lean_dec_ref(v_g_1908_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2007_, 1);
v_a_1921_ = v_a_2032_;
goto v___jp_1920_;
}
else
{
lean_dec_ref(v_e_1911_);
return v___x_2007_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v_canon_2034_; lean_object* v_cacheInType_2035_; lean_object* v___x_2036_; 
lean_dec_ref(v_g_1908_);
v___x_2033_ = lean_st_ref_get(v_a_1914_);
v_canon_2034_ = lean_ctor_get(v___x_2033_, 9);
lean_inc_ref(v_canon_2034_);
lean_dec(v___x_2033_);
v_cacheInType_2035_ = lean_ctor_get(v_canon_2034_, 1);
lean_inc_ref(v_cacheInType_2035_);
lean_dec_ref(v_canon_2034_);
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2035_, v_e_1911_);
lean_dec_ref(v_cacheInType_2035_);
if (lean_obj_tag(v___x_2036_) == 1)
{
lean_object* v_val_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_e_1911_);
lean_dec_ref(v_h_1910_);
lean_dec_ref(v_prop_1909_);
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_val_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 0);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_val_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v___x_2045_; 
lean_dec(v___x_2036_);
v___x_2045_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1909_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = 0;
v___x_2048_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1910_, v_a_2046_, v___x_2047_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
v___y_1955_ = v___x_2048_;
goto v___jp_1954_;
}
else
{
lean_dec_ref(v_h_1910_);
v___y_1955_ = v___x_2045_;
goto v___jp_1954_;
}
}
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v_canon_1923_; lean_object* v_share_1924_; lean_object* v_maxFVar_1925_; lean_object* v_proofInstInfo_1926_; lean_object* v_inferType_1927_; lean_object* v_getLevel_1928_; lean_object* v_congrInfo_1929_; lean_object* v_defEqI_1930_; lean_object* v_extensions_1931_; lean_object* v_issues_1932_; lean_object* v_instanceOverrides_1933_; uint8_t v_debug_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1953_; 
v___x_1922_ = lean_st_ref_take(v_a_1914_);
v_canon_1923_ = lean_ctor_get(v___x_1922_, 9);
v_share_1924_ = lean_ctor_get(v___x_1922_, 0);
v_maxFVar_1925_ = lean_ctor_get(v___x_1922_, 1);
v_proofInstInfo_1926_ = lean_ctor_get(v___x_1922_, 2);
v_inferType_1927_ = lean_ctor_get(v___x_1922_, 3);
v_getLevel_1928_ = lean_ctor_get(v___x_1922_, 4);
v_congrInfo_1929_ = lean_ctor_get(v___x_1922_, 5);
v_defEqI_1930_ = lean_ctor_get(v___x_1922_, 6);
v_extensions_1931_ = lean_ctor_get(v___x_1922_, 7);
v_issues_1932_ = lean_ctor_get(v___x_1922_, 8);
v_instanceOverrides_1933_ = lean_ctor_get(v___x_1922_, 10);
v_debug_1934_ = lean_ctor_get_uint8(v___x_1922_, sizeof(void*)*11);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1936_ = v___x_1922_;
v_isShared_1937_ = v_isSharedCheck_1953_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_instanceOverrides_1933_);
lean_inc(v_canon_1923_);
lean_inc(v_issues_1932_);
lean_inc(v_extensions_1931_);
lean_inc(v_defEqI_1930_);
lean_inc(v_congrInfo_1929_);
lean_inc(v_getLevel_1928_);
lean_inc(v_inferType_1927_);
lean_inc(v_proofInstInfo_1926_);
lean_inc(v_maxFVar_1925_);
lean_inc(v_share_1924_);
lean_dec(v___x_1922_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1953_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_cache_1938_; lean_object* v_cacheInType_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1952_; 
v_cache_1938_ = lean_ctor_get(v_canon_1923_, 0);
v_cacheInType_1939_ = lean_ctor_get(v_canon_1923_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_canon_1923_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1941_ = v_canon_1923_;
v_isShared_1942_ = v_isSharedCheck_1952_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_cacheInType_1939_);
lean_inc(v_cache_1938_);
lean_dec(v_canon_1923_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1952_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_inc_ref(v_a_1921_);
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1938_, v_e_1911_, v_a_1921_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_cacheInType_1939_);
v___x_1945_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 9, v___x_1945_);
v___x_1947_ = v___x_1936_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_share_1924_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_maxFVar_1925_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_proofInstInfo_1926_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_inferType_1927_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_getLevel_1928_);
lean_ctor_set(v_reuseFailAlloc_1950_, 5, v_congrInfo_1929_);
lean_ctor_set(v_reuseFailAlloc_1950_, 6, v_defEqI_1930_);
lean_ctor_set(v_reuseFailAlloc_1950_, 7, v_extensions_1931_);
lean_ctor_set(v_reuseFailAlloc_1950_, 8, v_issues_1932_);
lean_ctor_set(v_reuseFailAlloc_1950_, 9, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1950_, 10, v_instanceOverrides_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*11, v_debug_1934_);
v___x_1947_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_st_ref_set(v_a_1914_, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_a_1921_);
return v___x_1949_;
}
}
}
}
}
v___jp_1954_:
{
if (lean_obj_tag(v___y_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1994_; 
v_a_1956_ = lean_ctor_get(v___y_1955_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___y_1955_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1958_ = v___y_1955_;
v_isShared_1959_ = v_isSharedCheck_1994_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___y_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1994_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v_canon_1961_; lean_object* v_share_1962_; lean_object* v_maxFVar_1963_; lean_object* v_proofInstInfo_1964_; lean_object* v_inferType_1965_; lean_object* v_getLevel_1966_; lean_object* v_congrInfo_1967_; lean_object* v_defEqI_1968_; lean_object* v_extensions_1969_; lean_object* v_issues_1970_; lean_object* v_instanceOverrides_1971_; uint8_t v_debug_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1993_; 
v___x_1960_ = lean_st_ref_take(v_a_1914_);
v_canon_1961_ = lean_ctor_get(v___x_1960_, 9);
v_share_1962_ = lean_ctor_get(v___x_1960_, 0);
v_maxFVar_1963_ = lean_ctor_get(v___x_1960_, 1);
v_proofInstInfo_1964_ = lean_ctor_get(v___x_1960_, 2);
v_inferType_1965_ = lean_ctor_get(v___x_1960_, 3);
v_getLevel_1966_ = lean_ctor_get(v___x_1960_, 4);
v_congrInfo_1967_ = lean_ctor_get(v___x_1960_, 5);
v_defEqI_1968_ = lean_ctor_get(v___x_1960_, 6);
v_extensions_1969_ = lean_ctor_get(v___x_1960_, 7);
v_issues_1970_ = lean_ctor_get(v___x_1960_, 8);
v_instanceOverrides_1971_ = lean_ctor_get(v___x_1960_, 10);
v_debug_1972_ = lean_ctor_get_uint8(v___x_1960_, sizeof(void*)*11);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1974_ = v___x_1960_;
v_isShared_1975_ = v_isSharedCheck_1993_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_instanceOverrides_1971_);
lean_inc(v_canon_1961_);
lean_inc(v_issues_1970_);
lean_inc(v_extensions_1969_);
lean_inc(v_defEqI_1968_);
lean_inc(v_congrInfo_1967_);
lean_inc(v_getLevel_1966_);
lean_inc(v_inferType_1965_);
lean_inc(v_proofInstInfo_1964_);
lean_inc(v_maxFVar_1963_);
lean_inc(v_share_1962_);
lean_dec(v___x_1960_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1993_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_cache_1976_; lean_object* v_cacheInType_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1992_; 
v_cache_1976_ = lean_ctor_get(v_canon_1961_, 0);
v_cacheInType_1977_ = lean_ctor_get(v_canon_1961_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_canon_1961_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1979_ = v_canon_1961_;
v_isShared_1980_ = v_isSharedCheck_1992_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_cacheInType_1977_);
lean_inc(v_cache_1976_);
lean_dec(v_canon_1961_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1992_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_inc(v_a_1956_);
v___x_1981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1977_, v_e_1911_, v_a_1956_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1981_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_cache_1976_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 9, v___x_1983_);
v___x_1985_ = v___x_1974_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_share_1962_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_maxFVar_1963_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_proofInstInfo_1964_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_inferType_1965_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v_getLevel_1966_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_congrInfo_1967_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_defEqI_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_extensions_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_issues_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 9, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 10, v_instanceOverrides_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*11, v_debug_1972_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_st_ref_set(v_a_1914_, v___x_1985_);
if (v_isShared_1959_ == 0)
{
v___x_1988_ = v___x_1958_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1956_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1911_);
return v___y_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2049_, lean_object* v_a_2050_, lean_object* v___x_2051_, lean_object* v_snd_2052_, uint8_t v___x_2053_, lean_object* v_fst_2054_, lean_object* v_____r_2055_, uint8_t v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_arg_x27_2065_; lean_object* v___x_2077_; 
lean_inc_ref(v___x_2051_);
v___x_2077_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2049_, v_a_2050_, v___x_2051_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
switch(v___x_2079_)
{
case 0:
{
lean_object* v___x_2080_; 
lean_inc_ref(v___x_2051_);
v___x_2080_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_arg_x27_2065_ = v_a_2081_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
case 1:
{
lean_object* v___x_2090_; 
lean_inc_ref(v___x_2051_);
v___x_2090_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2051_, v___y_2060_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2110_ = l_Lean_Expr_cleanupAnnotations(v_a_2091_);
v___x_2111_ = l_Lean_Expr_isApp(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v___x_2110_);
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
v___y_2095_ = v___y_2058_;
v___y_2096_ = v___y_2059_;
v___y_2097_ = v___y_2060_;
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
goto v___jp_2092_;
}
else
{
lean_object* v_arg_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_arg_2112_ = lean_ctor_get(v___x_2110_, 1);
lean_inc_ref(v_arg_2112_);
v___x_2113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2110_);
v___x_2114_ = l_Lean_Expr_isApp(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_arg_2112_);
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
v___y_2095_ = v___y_2058_;
v___y_2096_ = v___y_2059_;
v___y_2097_ = v___y_2060_;
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
goto v___jp_2092_;
}
else
{
lean_object* v_arg_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_arg_2115_ = lean_ctor_get(v___x_2113_, 1);
lean_inc_ref(v_arg_2115_);
v___x_2116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2113_);
v___x_2117_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2118_ = l_Lean_Expr_isConstOf(v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2120_ = l_Lean_Expr_isConstOf(v___x_2116_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_dec_ref(v___x_2116_);
lean_dec_ref(v_arg_2115_);
lean_dec_ref(v_arg_2112_);
v___y_2093_ = v___y_2056_;
v___y_2094_ = v___y_2057_;
v___y_2095_ = v___y_2058_;
v___y_2096_ = v___y_2059_;
v___y_2097_ = v___y_2060_;
v___y_2098_ = v___y_2061_;
v___y_2099_ = v___y_2062_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2121_; 
lean_inc_ref(v___x_2051_);
v___x_2121_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2116_, v_arg_2115_, v_arg_2112_, v___x_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v_arg_x27_2065_ = v_a_2122_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2123_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2121_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
lean_object* v___x_2131_; 
lean_inc_ref(v___x_2051_);
v___x_2131_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2116_, v_arg_2115_, v_arg_2112_, v___x_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v_arg_x27_2065_ = v_a_2132_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2133_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2131_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
v___jp_2092_:
{
lean_object* v___x_2100_; 
lean_inc_ref(v___x_2051_);
v___x_2100_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2051_, v___x_2053_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v_arg_x27_2065_ = v_a_2101_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2102_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2100_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2141_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2090_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2090_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
default: 
{
lean_object* v___x_2149_; 
lean_inc_ref(v___x_2051_);
v___x_2149_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_arg_x27_2065_ = v_a_2150_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2151_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2149_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2149_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_fst_2054_);
lean_dec(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2159_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2077_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2077_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
v___jp_2064_:
{
size_t v___x_2066_; size_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = lean_ptr_addr(v___x_2051_);
lean_dec_ref(v___x_2051_);
v___x_2067_ = lean_ptr_addr(v_arg_x27_2065_);
v___x_2068_ = lean_usize_dec_eq(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_fst_2054_);
v___x_2069_ = lean_array_fset(v_snd_2052_, v_a_2050_, v_arg_x27_2065_);
v___x_2070_ = lean_box(v___x_2053_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref(v_arg_x27_2065_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_fst_2054_);
lean_ctor_set(v___x_2074_, 1, v_snd_2052_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2171_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2172_ = l_Lean_Name_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2182_, lean_object* v___x_2183_, lean_object* v_a_2184_, lean_object* v_b_2185_, uint8_t v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___y_2195_; uint8_t v___x_2217_; 
v___x_2217_ = lean_nat_dec_lt(v_a_2184_, v_upperBound_2182_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
lean_dec(v_a_2184_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_b_2185_);
return v___x_2218_;
}
else
{
lean_object* v_options_2219_; lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2285_; 
v_options_2219_ = lean_ctor_get(v___y_2191_, 2);
v_fst_2220_ = lean_ctor_get(v_b_2185_, 0);
v_snd_2221_ = lean_ctor_get(v_b_2185_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_b_2185_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2223_ = v_b_2185_;
v_isShared_2224_ = v_isSharedCheck_2285_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snd_2221_);
lean_inc(v_fst_2220_);
lean_dec(v_b_2185_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2285_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_inheritedTraceOptions_2225_; uint8_t v_hasTrace_2226_; lean_object* v___x_2227_; 
v_inheritedTraceOptions_2225_ = lean_ctor_get(v___y_2191_, 13);
v_hasTrace_2226_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
v___x_2227_ = lean_array_fget(v_snd_2221_, v_a_2184_);
if (v_hasTrace_2226_ == 0)
{
lean_del_object(v___x_2223_);
goto v___jp_2228_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2232_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2225_, v_options_2219_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_del_object(v___x_2223_);
goto v___jp_2228_;
}
else
{
lean_object* v___x_2234_; 
lean_inc(v___x_2227_);
v___x_2234_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2183_, v_a_2184_, v___x_2227_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___x_2227_);
v___x_2236_ = lean_infer_type(v___x_2227_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; lean_object* v___y_2240_; uint8_t v___x_2264_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2264_ = lean_unbox(v_a_2235_);
lean_dec(v_a_2235_);
switch(v___x_2264_)
{
case 0:
{
lean_object* v___x_2265_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2240_ = v___x_2265_;
goto v___jp_2239_;
}
case 1:
{
lean_object* v___x_2266_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2240_ = v___x_2266_;
goto v___jp_2239_;
}
case 2:
{
lean_object* v___x_2267_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2240_ = v___x_2267_;
goto v___jp_2239_;
}
default: 
{
lean_object* v___x_2268_; 
v___x_2268_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2240_ = v___x_2268_;
goto v___jp_2239_;
}
}
v___jp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_inc(v___y_2240_);
v___x_2241_ = l_Lean_MessageData_ofFormat(v___y_2240_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 7);
lean_ctor_set(v___x_2223_, 1, v___x_2241_);
lean_ctor_set(v___x_2223_, 0, v___x_2238_);
v___x_2243_ = v___x_2223_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2244_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
lean_inc(v___x_2227_);
v___x_2246_ = l_Lean_MessageData_ofExpr(v___x_2227_);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_MessageData_ofExpr(v_a_2237_);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2231_, v___x_2251_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2183_, v_a_2184_, v___x_2227_, v_snd_2221_, v___x_2217_, v_fst_2220_, v_a_2253_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
v___y_2195_ = v___x_2254_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2227_);
lean_dec(v_snd_2221_);
lean_dec(v_fst_2220_);
lean_dec(v_a_2184_);
v_a_2255_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2252_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2252_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_a_2235_);
lean_dec(v___x_2227_);
lean_del_object(v___x_2223_);
lean_dec(v_snd_2221_);
lean_dec(v_fst_2220_);
lean_dec(v_a_2184_);
v_a_2269_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2236_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2236_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v___x_2227_);
lean_del_object(v___x_2223_);
lean_dec(v_snd_2221_);
lean_dec(v_fst_2220_);
lean_dec(v_a_2184_);
v_a_2277_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2234_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2234_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
v___jp_2228_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2183_, v_a_2184_, v___x_2227_, v_snd_2221_, v___x_2217_, v_fst_2220_, v___x_2229_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
v___y_2195_ = v___x_2230_;
goto v___jp_2194_;
}
}
}
v___jp_2194_:
{
if (lean_obj_tag(v___y_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2208_; 
v_a_2196_ = lean_ctor_get(v___y_2195_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___y_2195_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2198_ = v___y_2195_;
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___y_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
if (lean_obj_tag(v_a_2196_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; 
lean_dec(v_a_2184_);
v_a_2200_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v_a_2196_, 1);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v_a_2200_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_del_object(v___x_2198_);
v_a_2204_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v_a_2196_, 1);
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_add(v_a_2184_, v___x_2205_);
lean_dec(v_a_2184_);
v_a_2184_ = v___x_2206_;
v_b_2185_ = v_a_2204_;
goto _start;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2184_);
v_a_2209_ = lean_ctor_get(v___y_2195_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___y_2195_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___y_2195_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___y_2195_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, uint8_t v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___y_2299_; uint8_t v_modified_2300_; lean_object* v_f_2301_; uint8_t v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v_args_2357_; uint8_t v_modified_2358_; uint8_t v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; 
if (lean_obj_tag(v_x_2287_) == 5)
{
lean_object* v_fn_2394_; lean_object* v_arg_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_fn_2394_ = lean_ctor_get(v_x_2287_, 0);
lean_inc_ref(v_fn_2394_);
v_arg_2395_ = lean_ctor_get(v_x_2287_, 1);
lean_inc_ref(v_arg_2395_);
lean_dec_ref_known(v_x_2287_, 2);
v___x_2396_ = lean_array_set(v_x_2288_, v_x_2289_, v_arg_2395_);
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_sub(v_x_2289_, v___x_2397_);
lean_dec(v_x_2289_);
v_x_2287_ = v_fn_2394_;
v_x_2288_ = v___x_2396_;
v_x_2289_ = v___x_2398_;
goto _start;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
lean_dec(v_x_2289_);
v___x_2400_ = lean_array_get_size(v_x_2288_);
v___x_2401_ = lean_unsigned_to_nat(2u);
v___x_2402_ = lean_nat_dec_eq(v___x_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
v___y_2373_ = v___y_2290_;
v___y_2374_ = v___y_2291_;
v___y_2375_ = v___y_2292_;
v___y_2376_ = v___y_2293_;
v___y_2377_ = v___y_2294_;
v___y_2378_ = v___y_2295_;
v___y_2379_ = v___y_2296_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2404_ = l_Lean_Expr_isConstOf(v_x_2287_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2406_ = l_Lean_Expr_isConstOf(v_x_2287_, v___x_2405_);
if (v___x_2406_ == 0)
{
v___y_2373_ = v___y_2290_;
v___y_2374_ = v___y_2291_;
v___y_2375_ = v___y_2292_;
v___y_2376_ = v___y_2293_;
v___y_2377_ = v___y_2294_;
v___y_2378_ = v___y_2295_;
v___y_2379_ = v___y_2296_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2407_ = l_Lean_instInhabitedExpr;
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_array_get(v___x_2407_, v_x_2288_, v___x_2408_);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_array_get(v___x_2407_, v_x_2288_, v___x_2410_);
lean_dec_ref(v_x_2288_);
v___x_2412_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2287_, v___x_2409_, v___x_2411_, v_e_2286_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2412_;
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v_prop_2415_; lean_object* v___x_2416_; 
v___x_2413_ = l_Lean_instInhabitedExpr;
v___x_2414_ = lean_unsigned_to_nat(0u);
v_prop_2415_ = lean_array_get_borrowed(v___x_2413_, v_x_2288_, v___x_2414_);
lean_inc(v_prop_2415_);
v___x_2416_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2415_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2433_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
size_t v___x_2421_; size_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_ptr_addr(v_prop_2415_);
v___x_2422_ = lean_ptr_addr(v_a_2417_);
v___x_2423_ = lean_usize_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
lean_dec_ref(v_e_2286_);
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_array_get(v___x_2413_, v_x_2288_, v___x_2424_);
lean_dec_ref(v_x_2288_);
v___x_2426_ = l_Lean_mkAppB(v_x_2287_, v_a_2417_, v___x_2425_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2426_);
v___x_2428_ = v___x_2419_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
else
{
lean_object* v___x_2431_; 
lean_dec(v_a_2417_);
lean_dec_ref(v_x_2288_);
lean_dec_ref(v_x_2287_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_e_2286_);
v___x_2431_ = v___x_2419_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_e_2286_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_dec_ref(v_x_2288_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_e_2286_);
return v___x_2416_;
}
}
}
}
v___jp_2298_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_box(0);
lean_inc_ref(v_f_2301_);
v___x_2310_ = l_Lean_Meta_getFunInfo(v_f_2301_, v___x_2309_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v_paramInfo_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2346_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v_paramInfo_2312_ = lean_ctor_get(v_a_2311_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_a_2311_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_a_2311_, 1);
lean_dec(v_unused_2347_);
v___x_2314_ = v_a_2311_;
v_isShared_2315_ = v_isSharedCheck_2346_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_paramInfo_2312_);
lean_dec(v_a_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2346_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2316_ = lean_array_get_size(v___y_2299_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_box(v_modified_2300_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___y_2299_);
lean_ctor_set(v___x_2314_, 0, v___x_2318_);
v___x_2320_ = v___x_2314_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___y_2299_);
v___x_2320_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2316_, v_paramInfo_2312_, v___x_2317_, v___x_2320_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec_ref(v_paramInfo_2312_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_fst_2326_; uint8_t v___x_2327_; 
v_fst_2326_ = lean_ctor_get(v_a_2322_, 0);
v___x_2327_ = lean_unbox(v_fst_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_a_2322_);
lean_dec_ref(v_f_2301_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_e_2286_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_e_2286_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
else
{
lean_object* v_snd_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec_ref(v_e_2286_);
v_snd_2331_ = lean_ctor_get(v_a_2322_, 1);
lean_inc(v_snd_2331_);
lean_dec(v_a_2322_);
v___x_2332_ = l_Lean_mkAppN(v_f_2301_, v_snd_2331_);
lean_dec(v_snd_2331_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2332_);
v___x_2334_ = v___x_2324_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
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
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_f_2301_);
lean_dec_ref(v_e_2286_);
v_a_2337_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2321_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2321_);
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
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v_f_2301_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v_e_2286_);
v_a_2348_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2310_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2310_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
v___jp_2356_:
{
lean_object* v___x_2366_; 
lean_inc_ref(v_x_2287_);
v___x_2366_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2287_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; size_t v___x_2368_; size_t v___x_2369_; uint8_t v___x_2370_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_ptr_addr(v_x_2287_);
v___x_2369_ = lean_ptr_addr(v_a_2367_);
v___x_2370_ = lean_usize_dec_eq(v___x_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
uint8_t v___x_2371_; 
lean_dec_ref(v_x_2287_);
v___x_2371_ = 1;
v___y_2299_ = v_args_2357_;
v_modified_2300_ = v___x_2371_;
v_f_2301_ = v_a_2367_;
v___y_2302_ = v___y_2359_;
v___y_2303_ = v___y_2360_;
v___y_2304_ = v___y_2361_;
v___y_2305_ = v___y_2362_;
v___y_2306_ = v___y_2363_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2365_;
goto v___jp_2298_;
}
else
{
lean_dec(v_a_2367_);
v___y_2299_ = v_args_2357_;
v_modified_2300_ = v_modified_2358_;
v_f_2301_ = v_x_2287_;
v___y_2302_ = v___y_2359_;
v___y_2303_ = v___y_2360_;
v___y_2304_ = v___y_2361_;
v___y_2305_ = v___y_2362_;
v___y_2306_ = v___y_2363_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2365_;
goto v___jp_2298_;
}
}
else
{
lean_dec_ref(v_args_2357_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_e_2286_);
return v___x_2366_;
}
}
v___jp_2372_:
{
uint8_t v_modified_2380_; lean_object* v___x_2381_; uint8_t v_modified_2382_; 
v_modified_2380_ = 0;
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2382_ = l_Lean_Expr_isConstOf(v_x_2287_, v___x_2381_);
if (v_modified_2382_ == 0)
{
v_args_2357_ = v_x_2288_;
v_modified_2358_ = v_modified_2380_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2375_;
v___y_2362_ = v___y_2376_;
v___y_2363_ = v___y_2377_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2383_; 
lean_inc_ref(v_x_2288_);
v___x_2383_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2288_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
if (lean_obj_tag(v_a_2384_) == 1)
{
lean_object* v_val_2385_; 
lean_dec_ref(v_x_2288_);
v_val_2385_ = lean_ctor_get(v_a_2384_, 0);
lean_inc(v_val_2385_);
lean_dec_ref_known(v_a_2384_, 1);
v_args_2357_ = v_val_2385_;
v_modified_2358_ = v_modified_2382_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2375_;
v___y_2362_ = v___y_2376_;
v___y_2363_ = v___y_2377_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
goto v___jp_2356_;
}
else
{
lean_dec(v_a_2384_);
v_args_2357_ = v_x_2288_;
v_modified_2358_ = v_modified_2380_;
v___y_2359_ = v___y_2373_;
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2375_;
v___y_2362_ = v___y_2376_;
v___y_2363_ = v___y_2377_;
v___y_2364_ = v___y_2378_;
v___y_2365_ = v___y_2379_;
goto v___jp_2356_;
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_x_2288_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_e_2286_);
v_a_2386_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2383_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2383_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2434_, uint8_t v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_dummy_2443_; lean_object* v_nargs_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_dummy_2443_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2444_ = l_Lean_Expr_getAppNumArgs(v_e_2434_);
lean_inc(v_nargs_2444_);
v___x_2445_ = lean_mk_array(v_nargs_2444_, v_dummy_2443_);
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_nat_sub(v_nargs_2444_, v___x_2446_);
lean_dec(v_nargs_2444_);
lean_inc_ref(v_e_2434_);
v___x_2448_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2434_, v_e_2434_, v___x_2445_, v___x_2447_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2449_, uint8_t v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2459_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
return v___x_2460_;
}
else
{
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2461_, uint8_t v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2461_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
if (lean_obj_tag(v_a_2471_) == 0)
{
lean_object* v_val_2472_; lean_object* v___x_2473_; 
lean_dec_ref(v_e_2461_);
v_val_2472_ = lean_ctor_get(v_a_2471_, 0);
lean_inc_ref(v_val_2472_);
lean_dec_ref_known(v_a_2471_, 1);
v___x_2473_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2472_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2473_;
}
else
{
lean_object* v___x_2474_; 
lean_dec(v_a_2471_);
v___x_2474_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2475_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2486_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
if (lean_obj_tag(v_a_2477_) == 0)
{
lean_object* v_val_2481_; lean_object* v___x_2482_; 
lean_del_object(v___x_2479_);
lean_dec(v_a_2475_);
v_val_2481_ = lean_ctor_get(v_a_2477_, 0);
lean_inc_ref(v_val_2481_);
lean_dec_ref_known(v_a_2477_, 1);
v___x_2482_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2481_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2482_;
}
else
{
lean_object* v___x_2484_; 
lean_dec(v_a_2477_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_a_2475_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2475_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2475_);
v_a_2487_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2476_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2476_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_e_2461_);
v_a_2495_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2470_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2470_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2509_, uint8_t v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2518_; 
lean_inc_ref(v_e_2509_);
v___x_2518_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2509_, v_a_2514_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2530_ = l_Lean_Expr_cleanupAnnotations(v_a_2519_);
v___x_2531_ = l_Lean_Expr_isApp(v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v___x_2530_);
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
v___y_2523_ = v_a_2512_;
v___y_2524_ = v_a_2513_;
v___y_2525_ = v_a_2514_;
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
goto v___jp_2520_;
}
else
{
lean_object* v_arg_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_arg_2532_ = lean_ctor_get(v___x_2530_, 1);
lean_inc_ref(v_arg_2532_);
v___x_2533_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2530_);
v___x_2534_ = l_Lean_Expr_isApp(v___x_2533_);
if (v___x_2534_ == 0)
{
lean_dec_ref(v___x_2533_);
lean_dec_ref(v_arg_2532_);
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
v___y_2523_ = v_a_2512_;
v___y_2524_ = v_a_2513_;
v___y_2525_ = v_a_2514_;
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
goto v___jp_2520_;
}
else
{
lean_object* v_arg_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_arg_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc_ref(v_arg_2535_);
v___x_2536_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2533_);
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2538_ = l_Lean_Expr_isConstOf(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_dec_ref(v___x_2536_);
lean_dec_ref(v_arg_2535_);
lean_dec_ref(v_arg_2532_);
v___y_2521_ = v_a_2510_;
v___y_2522_ = v_a_2511_;
v___y_2523_ = v_a_2512_;
v___y_2524_ = v_a_2513_;
v___y_2525_ = v_a_2514_;
v___y_2526_ = v_a_2515_;
v___y_2527_ = v_a_2516_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2536_, v_arg_2535_, v_arg_2532_, v_e_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
return v___x_2539_;
}
}
}
v___jp_2520_:
{
uint8_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = 0;
v___x_2529_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2509_, v___x_2528_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2529_;
}
}
else
{
lean_dec_ref(v_e_2509_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2540_, lean_object* v_00_u03b1_2541_, lean_object* v_c_2542_, lean_object* v_inst_2543_, lean_object* v_a_2544_, lean_object* v_b_2545_, uint8_t v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2542_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; uint8_t v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_n(v_a_2555_, 2);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2555_);
if (v___x_2556_ == 0)
{
uint8_t v___x_2557_; 
lean_inc(v_a_2555_);
v___x_2557_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2555_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2541_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2543_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2544_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = l_Lean_mkApp5(v_f_2540_, v_a_2559_, v_a_2555_, v_a_2561_, v_a_2563_, v_a_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
lean_dec(v_a_2563_);
lean_dec(v_a_2561_);
lean_dec(v_a_2559_);
lean_dec(v_a_2555_);
lean_dec_ref(v_f_2540_);
return v___x_2564_;
}
}
else
{
lean_dec(v_a_2561_);
lean_dec(v_a_2559_);
lean_dec(v_a_2555_);
lean_dec_ref(v_b_2545_);
lean_dec_ref(v_f_2540_);
return v___x_2562_;
}
}
else
{
lean_dec(v_a_2559_);
lean_dec(v_a_2555_);
lean_dec_ref(v_b_2545_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_f_2540_);
return v___x_2560_;
}
}
else
{
lean_dec(v_a_2555_);
lean_dec_ref(v_b_2545_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_f_2540_);
return v___x_2558_;
}
}
else
{
lean_object* v___x_2574_; 
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_00_u03b1_2541_);
lean_dec_ref(v_f_2540_);
v___x_2574_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2575_; 
lean_dec(v_a_2555_);
lean_dec_ref(v_b_2545_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_00_u03b1_2541_);
lean_dec_ref(v_f_2540_);
v___x_2575_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2544_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2575_;
}
}
else
{
lean_dec_ref(v_b_2545_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_00_u03b1_2541_);
lean_dec_ref(v_f_2540_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2576_, lean_object* v_00_u03b1_2577_, lean_object* v_c_2578_, lean_object* v_a_2579_, lean_object* v_b_2580_, uint8_t v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2578_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc_n(v_a_2590_, 2);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_Lean_Expr_isBoolTrue(v_a_2590_);
if (v___x_2591_ == 0)
{
uint8_t v___x_2592_; 
lean_inc(v_a_2590_);
v___x_2592_ = l_Lean_Expr_isBoolFalse(v_a_2590_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2577_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2579_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2606_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2606_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2606_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2602_ = l_Lean_mkApp4(v_f_2576_, v_a_2594_, v_a_2590_, v_a_2596_, v_a_2598_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2602_);
v___x_2604_ = v___x_2600_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
else
{
lean_dec(v_a_2596_);
lean_dec(v_a_2594_);
lean_dec(v_a_2590_);
lean_dec_ref(v_f_2576_);
return v___x_2597_;
}
}
else
{
lean_dec(v_a_2594_);
lean_dec(v_a_2590_);
lean_dec_ref(v_b_2580_);
lean_dec_ref(v_f_2576_);
return v___x_2595_;
}
}
else
{
lean_dec(v_a_2590_);
lean_dec_ref(v_b_2580_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_f_2576_);
return v___x_2593_;
}
}
else
{
lean_object* v___x_2607_; 
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_00_u03b1_2577_);
lean_dec_ref(v_f_2576_);
v___x_2607_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v___x_2607_;
}
}
else
{
lean_object* v___x_2608_; 
lean_dec(v_a_2590_);
lean_dec_ref(v_b_2580_);
lean_dec_ref(v_00_u03b1_2577_);
lean_dec_ref(v_f_2576_);
v___x_2608_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2579_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v___x_2608_;
}
}
else
{
lean_dec_ref(v_b_2580_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_00_u03b1_2577_);
lean_dec_ref(v_f_2576_);
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2609_, uint8_t v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2618_; 
lean_inc_ref(v_e_2609_);
v___x_2618_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2609_, v_a_2614_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; uint8_t v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2644_ = l_Lean_Expr_cleanupAnnotations(v_a_2619_);
v___x_2645_ = l_Lean_Expr_isApp(v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v___x_2644_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v_arg_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_arg_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc_ref(v_arg_2646_);
v___x_2647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2644_);
v___x_2648_ = l_Lean_Expr_isApp(v___x_2647_);
if (v___x_2648_ == 0)
{
lean_dec_ref(v___x_2647_);
lean_dec_ref(v_arg_2646_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v_arg_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v_arg_2649_ = lean_ctor_get(v___x_2647_, 1);
lean_inc_ref(v_arg_2649_);
v___x_2650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2647_);
v___x_2651_ = l_Lean_Expr_isApp(v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec_ref(v___x_2650_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v_arg_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_arg_2652_ = lean_ctor_get(v___x_2650_, 1);
lean_inc_ref(v_arg_2652_);
v___x_2653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2650_);
v___x_2654_ = l_Lean_Expr_isApp(v___x_2653_);
if (v___x_2654_ == 0)
{
lean_dec_ref(v___x_2653_);
lean_dec_ref(v_arg_2652_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v_arg_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_arg_2655_ = lean_ctor_get(v___x_2653_, 1);
lean_inc_ref(v_arg_2655_);
v___x_2656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2653_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2658_ = l_Lean_Expr_isConstOf(v___x_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
v___x_2659_ = l_Lean_Expr_isApp(v___x_2656_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_arg_2655_);
lean_dec_ref(v_arg_2652_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v_arg_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_arg_2660_ = lean_ctor_get(v___x_2656_, 1);
lean_inc_ref(v_arg_2660_);
v___x_2661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2656_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2663_ = l_Lean_Expr_isConstOf(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_dec_ref(v___x_2661_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2655_);
lean_dec_ref(v_arg_2652_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
v___y_2621_ = v_a_2610_;
v___y_2622_ = v_a_2611_;
v___y_2623_ = v_a_2612_;
v___y_2624_ = v_a_2613_;
v___y_2625_ = v_a_2614_;
v___y_2626_ = v_a_2615_;
v___y_2627_ = v_a_2616_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2664_; 
lean_dec_ref(v_e_2609_);
v___x_2664_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2661_, v_arg_2660_, v_arg_2655_, v_arg_2652_, v_arg_2649_, v_arg_2646_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
return v___x_2664_;
}
}
}
else
{
lean_object* v___x_2665_; 
lean_dec_ref(v_e_2609_);
v___x_2665_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2656_, v_arg_2655_, v_arg_2652_, v_arg_2649_, v_arg_2646_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
return v___x_2665_;
}
}
}
}
}
v___jp_2620_:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Expr_getAppFn(v_e_2609_);
if (lean_obj_tag(v___x_2628_) == 4)
{
lean_object* v_declName_2629_; lean_object* v___x_2630_; 
v_declName_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_declName_2629_);
lean_dec_ref_known(v___x_2628_, 2);
v___x_2630_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2629_, v___y_2627_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; uint8_t v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = lean_unbox(v_a_2631_);
lean_dec(v_a_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2609_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2609_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2634_;
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_e_2609_);
v_a_2635_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2630_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2630_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2643_; 
lean_dec_ref(v___x_2628_);
v___x_2643_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2609_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2643_;
}
}
}
else
{
lean_dec_ref(v_e_2609_);
return v___x_2618_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2670_ = lean_unsigned_to_nat(18u);
v___x_2671_ = lean_unsigned_to_nat(1896u);
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2674_ = l_mkPanicMessageWithDecl(v___x_2673_, v___x_2672_, v___x_2671_, v___x_2670_, v___x_2669_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2675_, uint8_t v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = l_Lean_Expr_projExpr_x21(v_e_2675_);
v___x_2685_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2684_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___y_2688_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
if (lean_obj_tag(v_e_2675_) == 11)
{
lean_object* v_typeName_2710_; lean_object* v_idx_2711_; lean_object* v_struct_2712_; size_t v___x_2713_; size_t v___x_2714_; uint8_t v___x_2715_; 
v_typeName_2710_ = lean_ctor_get(v_e_2675_, 0);
v_idx_2711_ = lean_ctor_get(v_e_2675_, 1);
v_struct_2712_ = lean_ctor_get(v_e_2675_, 2);
v___x_2713_ = lean_ptr_addr(v_struct_2712_);
v___x_2714_ = lean_ptr_addr(v_a_2686_);
v___x_2715_ = lean_usize_dec_eq(v___x_2713_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_inc(v_idx_2711_);
lean_inc(v_typeName_2710_);
lean_dec_ref_known(v_e_2675_, 3);
v___x_2716_ = l_Lean_Expr_proj___override(v_typeName_2710_, v_idx_2711_, v_a_2686_);
v___y_2688_ = v___x_2716_;
goto v___jp_2687_;
}
else
{
lean_dec(v_a_2686_);
v___y_2688_ = v_e_2675_;
goto v___jp_2687_;
}
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec(v_a_2686_);
lean_dec_ref(v_e_2675_);
v___x_2717_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2718_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2717_);
v___y_2688_ = v___x_2718_;
goto v___jp_2687_;
}
v___jp_2687_:
{
lean_object* v___x_2689_; 
lean_inc_ref(v___y_2688_);
v___x_2689_ = l_Lean_Meta_reduceProj_x3f(v___y_2688_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2701_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
if (lean_obj_tag(v_a_2690_) == 0)
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___y_2688_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___y_2688_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2699_; 
lean_dec_ref(v___y_2688_);
v_val_2697_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_a_2690_, 1);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_val_2697_);
v___x_2699_ = v___x_2692_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_val_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v___y_2688_);
v_a_2702_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2689_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2689_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2675_);
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2719_, uint8_t v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
switch(lean_obj_tag(v_e_2719_))
{
case 7:
{
lean_object* v___x_2728_; 
v___x_2728_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2720_ == 0)
{
lean_object* v___x_2729_; lean_object* v_canon_2730_; lean_object* v_cache_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_st_ref_get(v_a_2722_);
v_canon_2730_ = lean_ctor_get(v___x_2729_, 9);
lean_inc_ref(v_canon_2730_);
lean_dec(v___x_2729_);
v_cache_2731_ = lean_ctor_get(v_canon_2730_, 0);
lean_inc_ref(v_cache_2731_);
lean_dec_ref(v_canon_2730_);
v___x_2732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2731_, v_e_2719_);
lean_dec_ref(v_cache_2731_);
if (lean_obj_tag(v___x_2732_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_val_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 0);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_val_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v___x_2741_; 
lean_dec(v___x_2732_);
lean_inc_ref(v_e_2719_);
v___x_2741_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2728_, v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2780_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2780_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2780_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v_canon_2747_; lean_object* v_share_2748_; lean_object* v_maxFVar_2749_; lean_object* v_proofInstInfo_2750_; lean_object* v_inferType_2751_; lean_object* v_getLevel_2752_; lean_object* v_congrInfo_2753_; lean_object* v_defEqI_2754_; lean_object* v_extensions_2755_; lean_object* v_issues_2756_; lean_object* v_instanceOverrides_2757_; uint8_t v_debug_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2779_; 
v___x_2746_ = lean_st_ref_take(v_a_2722_);
v_canon_2747_ = lean_ctor_get(v___x_2746_, 9);
v_share_2748_ = lean_ctor_get(v___x_2746_, 0);
v_maxFVar_2749_ = lean_ctor_get(v___x_2746_, 1);
v_proofInstInfo_2750_ = lean_ctor_get(v___x_2746_, 2);
v_inferType_2751_ = lean_ctor_get(v___x_2746_, 3);
v_getLevel_2752_ = lean_ctor_get(v___x_2746_, 4);
v_congrInfo_2753_ = lean_ctor_get(v___x_2746_, 5);
v_defEqI_2754_ = lean_ctor_get(v___x_2746_, 6);
v_extensions_2755_ = lean_ctor_get(v___x_2746_, 7);
v_issues_2756_ = lean_ctor_get(v___x_2746_, 8);
v_instanceOverrides_2757_ = lean_ctor_get(v___x_2746_, 10);
v_debug_2758_ = lean_ctor_get_uint8(v___x_2746_, sizeof(void*)*11);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2760_ = v___x_2746_;
v_isShared_2761_ = v_isSharedCheck_2779_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_instanceOverrides_2757_);
lean_inc(v_canon_2747_);
lean_inc(v_issues_2756_);
lean_inc(v_extensions_2755_);
lean_inc(v_defEqI_2754_);
lean_inc(v_congrInfo_2753_);
lean_inc(v_getLevel_2752_);
lean_inc(v_inferType_2751_);
lean_inc(v_proofInstInfo_2750_);
lean_inc(v_maxFVar_2749_);
lean_inc(v_share_2748_);
lean_dec(v___x_2746_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2779_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_cache_2762_; lean_object* v_cacheInType_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2778_; 
v_cache_2762_ = lean_ctor_get(v_canon_2747_, 0);
v_cacheInType_2763_ = lean_ctor_get(v_canon_2747_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_canon_2747_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2765_ = v_canon_2747_;
v_isShared_2766_ = v_isSharedCheck_2778_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_cacheInType_2763_);
lean_inc(v_cache_2762_);
lean_dec(v_canon_2747_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2778_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_inc(v_a_2742_);
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2762_, v_e_2719_, v_a_2742_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2767_);
v___x_2769_ = v___x_2765_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_cacheInType_2763_);
v___x_2769_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2771_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 9, v___x_2769_);
v___x_2771_ = v___x_2760_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_share_2748_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_maxFVar_2749_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_proofInstInfo_2750_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_inferType_2751_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_getLevel_2752_);
lean_ctor_set(v_reuseFailAlloc_2776_, 5, v_congrInfo_2753_);
lean_ctor_set(v_reuseFailAlloc_2776_, 6, v_defEqI_2754_);
lean_ctor_set(v_reuseFailAlloc_2776_, 7, v_extensions_2755_);
lean_ctor_set(v_reuseFailAlloc_2776_, 8, v_issues_2756_);
lean_ctor_set(v_reuseFailAlloc_2776_, 9, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2776_, 10, v_instanceOverrides_2757_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*11, v_debug_2758_);
v___x_2771_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_st_ref_set(v_a_2722_, v___x_2771_);
if (v_isShared_2745_ == 0)
{
v___x_2774_ = v___x_2744_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2742_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_2741_;
}
}
}
else
{
lean_object* v___x_2781_; lean_object* v_canon_2782_; lean_object* v_cacheInType_2783_; lean_object* v___x_2784_; 
v___x_2781_ = lean_st_ref_get(v_a_2722_);
v_canon_2782_ = lean_ctor_get(v___x_2781_, 9);
lean_inc_ref(v_canon_2782_);
lean_dec(v___x_2781_);
v_cacheInType_2783_ = lean_ctor_get(v_canon_2782_, 1);
lean_inc_ref(v_cacheInType_2783_);
lean_dec_ref(v_canon_2782_);
v___x_2784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2783_, v_e_2719_);
lean_dec_ref(v_cacheInType_2783_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v_val_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_val_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 0);
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_val_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec(v___x_2784_);
lean_inc_ref(v_e_2719_);
v___x_2793_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2728_, v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2832_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2832_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2832_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v_canon_2799_; lean_object* v_share_2800_; lean_object* v_maxFVar_2801_; lean_object* v_proofInstInfo_2802_; lean_object* v_inferType_2803_; lean_object* v_getLevel_2804_; lean_object* v_congrInfo_2805_; lean_object* v_defEqI_2806_; lean_object* v_extensions_2807_; lean_object* v_issues_2808_; lean_object* v_instanceOverrides_2809_; uint8_t v_debug_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2831_; 
v___x_2798_ = lean_st_ref_take(v_a_2722_);
v_canon_2799_ = lean_ctor_get(v___x_2798_, 9);
v_share_2800_ = lean_ctor_get(v___x_2798_, 0);
v_maxFVar_2801_ = lean_ctor_get(v___x_2798_, 1);
v_proofInstInfo_2802_ = lean_ctor_get(v___x_2798_, 2);
v_inferType_2803_ = lean_ctor_get(v___x_2798_, 3);
v_getLevel_2804_ = lean_ctor_get(v___x_2798_, 4);
v_congrInfo_2805_ = lean_ctor_get(v___x_2798_, 5);
v_defEqI_2806_ = lean_ctor_get(v___x_2798_, 6);
v_extensions_2807_ = lean_ctor_get(v___x_2798_, 7);
v_issues_2808_ = lean_ctor_get(v___x_2798_, 8);
v_instanceOverrides_2809_ = lean_ctor_get(v___x_2798_, 10);
v_debug_2810_ = lean_ctor_get_uint8(v___x_2798_, sizeof(void*)*11);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2812_ = v___x_2798_;
v_isShared_2813_ = v_isSharedCheck_2831_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_instanceOverrides_2809_);
lean_inc(v_canon_2799_);
lean_inc(v_issues_2808_);
lean_inc(v_extensions_2807_);
lean_inc(v_defEqI_2806_);
lean_inc(v_congrInfo_2805_);
lean_inc(v_getLevel_2804_);
lean_inc(v_inferType_2803_);
lean_inc(v_proofInstInfo_2802_);
lean_inc(v_maxFVar_2801_);
lean_inc(v_share_2800_);
lean_dec(v___x_2798_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2831_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v_cache_2814_; lean_object* v_cacheInType_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2830_; 
v_cache_2814_ = lean_ctor_get(v_canon_2799_, 0);
v_cacheInType_2815_ = lean_ctor_get(v_canon_2799_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_canon_2799_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2817_ = v_canon_2799_;
v_isShared_2818_ = v_isSharedCheck_2830_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_cacheInType_2815_);
lean_inc(v_cache_2814_);
lean_dec(v_canon_2799_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2830_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
lean_inc(v_a_2794_);
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2815_, v_e_2719_, v_a_2794_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_cache_2814_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 9, v___x_2821_);
v___x_2823_ = v___x_2812_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_share_2800_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_maxFVar_2801_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_proofInstInfo_2802_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_inferType_2803_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_getLevel_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_congrInfo_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_defEqI_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_extensions_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_issues_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 9, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2828_, 10, v_instanceOverrides_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*11, v_debug_2810_);
v___x_2823_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = lean_st_ref_set(v_a_2722_, v___x_2823_);
if (v_isShared_2797_ == 0)
{
v___x_2826_ = v___x_2796_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2794_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_2793_;
}
}
}
}
case 6:
{
if (v_a_2720_ == 0)
{
lean_object* v___x_2833_; lean_object* v_canon_2834_; lean_object* v_cache_2835_; lean_object* v___x_2836_; 
v___x_2833_ = lean_st_ref_get(v_a_2722_);
v_canon_2834_ = lean_ctor_get(v___x_2833_, 9);
lean_inc_ref(v_canon_2834_);
lean_dec(v___x_2833_);
v_cache_2835_ = lean_ctor_get(v_canon_2834_, 0);
lean_inc_ref(v_cache_2835_);
lean_dec_ref(v_canon_2834_);
v___x_2836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2835_, v_e_2719_);
lean_dec_ref(v_cache_2835_);
if (lean_obj_tag(v___x_2836_) == 1)
{
lean_object* v_val_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_val_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 0);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_val_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v___x_2845_; 
lean_dec(v___x_2836_);
lean_inc_ref(v_e_2719_);
v___x_2845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2884_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2884_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2884_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v_canon_2851_; lean_object* v_share_2852_; lean_object* v_maxFVar_2853_; lean_object* v_proofInstInfo_2854_; lean_object* v_inferType_2855_; lean_object* v_getLevel_2856_; lean_object* v_congrInfo_2857_; lean_object* v_defEqI_2858_; lean_object* v_extensions_2859_; lean_object* v_issues_2860_; lean_object* v_instanceOverrides_2861_; uint8_t v_debug_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2883_; 
v___x_2850_ = lean_st_ref_take(v_a_2722_);
v_canon_2851_ = lean_ctor_get(v___x_2850_, 9);
v_share_2852_ = lean_ctor_get(v___x_2850_, 0);
v_maxFVar_2853_ = lean_ctor_get(v___x_2850_, 1);
v_proofInstInfo_2854_ = lean_ctor_get(v___x_2850_, 2);
v_inferType_2855_ = lean_ctor_get(v___x_2850_, 3);
v_getLevel_2856_ = lean_ctor_get(v___x_2850_, 4);
v_congrInfo_2857_ = lean_ctor_get(v___x_2850_, 5);
v_defEqI_2858_ = lean_ctor_get(v___x_2850_, 6);
v_extensions_2859_ = lean_ctor_get(v___x_2850_, 7);
v_issues_2860_ = lean_ctor_get(v___x_2850_, 8);
v_instanceOverrides_2861_ = lean_ctor_get(v___x_2850_, 10);
v_debug_2862_ = lean_ctor_get_uint8(v___x_2850_, sizeof(void*)*11);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2864_ = v___x_2850_;
v_isShared_2865_ = v_isSharedCheck_2883_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_instanceOverrides_2861_);
lean_inc(v_canon_2851_);
lean_inc(v_issues_2860_);
lean_inc(v_extensions_2859_);
lean_inc(v_defEqI_2858_);
lean_inc(v_congrInfo_2857_);
lean_inc(v_getLevel_2856_);
lean_inc(v_inferType_2855_);
lean_inc(v_proofInstInfo_2854_);
lean_inc(v_maxFVar_2853_);
lean_inc(v_share_2852_);
lean_dec(v___x_2850_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2883_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_cache_2866_; lean_object* v_cacheInType_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2882_; 
v_cache_2866_ = lean_ctor_get(v_canon_2851_, 0);
v_cacheInType_2867_ = lean_ctor_get(v_canon_2851_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_canon_2851_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2869_ = v_canon_2851_;
v_isShared_2870_ = v_isSharedCheck_2882_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_cacheInType_2867_);
lean_inc(v_cache_2866_);
lean_dec(v_canon_2851_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2882_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_inc(v_a_2846_);
v___x_2871_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2866_, v_e_2719_, v_a_2846_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_cacheInType_2867_);
v___x_2873_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 9, v___x_2873_);
v___x_2875_ = v___x_2864_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_share_2852_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_maxFVar_2853_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_proofInstInfo_2854_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_inferType_2855_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_getLevel_2856_);
lean_ctor_set(v_reuseFailAlloc_2880_, 5, v_congrInfo_2857_);
lean_ctor_set(v_reuseFailAlloc_2880_, 6, v_defEqI_2858_);
lean_ctor_set(v_reuseFailAlloc_2880_, 7, v_extensions_2859_);
lean_ctor_set(v_reuseFailAlloc_2880_, 8, v_issues_2860_);
lean_ctor_set(v_reuseFailAlloc_2880_, 9, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2880_, 10, v_instanceOverrides_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*11, v_debug_2862_);
v___x_2875_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_st_ref_set(v_a_2722_, v___x_2875_);
if (v_isShared_2849_ == 0)
{
v___x_2878_ = v___x_2848_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2846_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_2845_;
}
}
}
else
{
lean_object* v___x_2885_; lean_object* v_canon_2886_; lean_object* v_cacheInType_2887_; lean_object* v___x_2888_; 
v___x_2885_ = lean_st_ref_get(v_a_2722_);
v_canon_2886_ = lean_ctor_get(v___x_2885_, 9);
lean_inc_ref(v_canon_2886_);
lean_dec(v___x_2885_);
v_cacheInType_2887_ = lean_ctor_get(v_canon_2886_, 1);
lean_inc_ref(v_cacheInType_2887_);
lean_dec_ref(v_canon_2886_);
v___x_2888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2887_, v_e_2719_);
lean_dec_ref(v_cacheInType_2887_);
if (lean_obj_tag(v___x_2888_) == 1)
{
lean_object* v_val_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_val_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 0);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_val_2889_);
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
lean_object* v___x_2897_; 
lean_dec(v___x_2888_);
lean_inc_ref(v_e_2719_);
v___x_2897_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2936_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2936_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2936_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v_canon_2903_; lean_object* v_share_2904_; lean_object* v_maxFVar_2905_; lean_object* v_proofInstInfo_2906_; lean_object* v_inferType_2907_; lean_object* v_getLevel_2908_; lean_object* v_congrInfo_2909_; lean_object* v_defEqI_2910_; lean_object* v_extensions_2911_; lean_object* v_issues_2912_; lean_object* v_instanceOverrides_2913_; uint8_t v_debug_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2935_; 
v___x_2902_ = lean_st_ref_take(v_a_2722_);
v_canon_2903_ = lean_ctor_get(v___x_2902_, 9);
v_share_2904_ = lean_ctor_get(v___x_2902_, 0);
v_maxFVar_2905_ = lean_ctor_get(v___x_2902_, 1);
v_proofInstInfo_2906_ = lean_ctor_get(v___x_2902_, 2);
v_inferType_2907_ = lean_ctor_get(v___x_2902_, 3);
v_getLevel_2908_ = lean_ctor_get(v___x_2902_, 4);
v_congrInfo_2909_ = lean_ctor_get(v___x_2902_, 5);
v_defEqI_2910_ = lean_ctor_get(v___x_2902_, 6);
v_extensions_2911_ = lean_ctor_get(v___x_2902_, 7);
v_issues_2912_ = lean_ctor_get(v___x_2902_, 8);
v_instanceOverrides_2913_ = lean_ctor_get(v___x_2902_, 10);
v_debug_2914_ = lean_ctor_get_uint8(v___x_2902_, sizeof(void*)*11);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2916_ = v___x_2902_;
v_isShared_2917_ = v_isSharedCheck_2935_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_instanceOverrides_2913_);
lean_inc(v_canon_2903_);
lean_inc(v_issues_2912_);
lean_inc(v_extensions_2911_);
lean_inc(v_defEqI_2910_);
lean_inc(v_congrInfo_2909_);
lean_inc(v_getLevel_2908_);
lean_inc(v_inferType_2907_);
lean_inc(v_proofInstInfo_2906_);
lean_inc(v_maxFVar_2905_);
lean_inc(v_share_2904_);
lean_dec(v___x_2902_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2935_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_cache_2918_; lean_object* v_cacheInType_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2934_; 
v_cache_2918_ = lean_ctor_get(v_canon_2903_, 0);
v_cacheInType_2919_ = lean_ctor_get(v_canon_2903_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_canon_2903_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2921_ = v_canon_2903_;
v_isShared_2922_ = v_isSharedCheck_2934_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_cacheInType_2919_);
lean_inc(v_cache_2918_);
lean_dec(v_canon_2903_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2934_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
lean_inc(v_a_2898_);
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2919_, v_e_2719_, v_a_2898_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2923_);
v___x_2925_ = v___x_2921_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_cache_2918_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2927_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 9, v___x_2925_);
v___x_2927_ = v___x_2916_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_share_2904_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_maxFVar_2905_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_proofInstInfo_2906_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_inferType_2907_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_getLevel_2908_);
lean_ctor_set(v_reuseFailAlloc_2932_, 5, v_congrInfo_2909_);
lean_ctor_set(v_reuseFailAlloc_2932_, 6, v_defEqI_2910_);
lean_ctor_set(v_reuseFailAlloc_2932_, 7, v_extensions_2911_);
lean_ctor_set(v_reuseFailAlloc_2932_, 8, v_issues_2912_);
lean_ctor_set(v_reuseFailAlloc_2932_, 9, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2932_, 10, v_instanceOverrides_2913_);
lean_ctor_set_uint8(v_reuseFailAlloc_2932_, sizeof(void*)*11, v_debug_2914_);
v___x_2927_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = lean_st_ref_set(v_a_2722_, v___x_2927_);
if (v_isShared_2901_ == 0)
{
v___x_2930_ = v___x_2900_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2898_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_2897_;
}
}
}
}
case 8:
{
lean_object* v___x_2937_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2720_ == 0)
{
lean_object* v___x_2938_; lean_object* v_canon_2939_; lean_object* v_cache_2940_; lean_object* v___x_2941_; 
v___x_2938_ = lean_st_ref_get(v_a_2722_);
v_canon_2939_ = lean_ctor_get(v___x_2938_, 9);
lean_inc_ref(v_canon_2939_);
lean_dec(v___x_2938_);
v_cache_2940_ = lean_ctor_get(v_canon_2939_, 0);
lean_inc_ref(v_cache_2940_);
lean_dec_ref(v_canon_2939_);
v___x_2941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2940_, v_e_2719_);
lean_dec_ref(v_cache_2940_);
if (lean_obj_tag(v___x_2941_) == 1)
{
lean_object* v_val_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref_known(v_e_2719_, 4);
v_val_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_val_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 0);
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_val_2942_);
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
lean_object* v___x_2950_; 
lean_dec(v___x_2941_);
lean_inc_ref(v_e_2719_);
v___x_2950_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2937_, v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2989_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2989_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2989_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v_canon_2956_; lean_object* v_share_2957_; lean_object* v_maxFVar_2958_; lean_object* v_proofInstInfo_2959_; lean_object* v_inferType_2960_; lean_object* v_getLevel_2961_; lean_object* v_congrInfo_2962_; lean_object* v_defEqI_2963_; lean_object* v_extensions_2964_; lean_object* v_issues_2965_; lean_object* v_instanceOverrides_2966_; uint8_t v_debug_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2988_; 
v___x_2955_ = lean_st_ref_take(v_a_2722_);
v_canon_2956_ = lean_ctor_get(v___x_2955_, 9);
v_share_2957_ = lean_ctor_get(v___x_2955_, 0);
v_maxFVar_2958_ = lean_ctor_get(v___x_2955_, 1);
v_proofInstInfo_2959_ = lean_ctor_get(v___x_2955_, 2);
v_inferType_2960_ = lean_ctor_get(v___x_2955_, 3);
v_getLevel_2961_ = lean_ctor_get(v___x_2955_, 4);
v_congrInfo_2962_ = lean_ctor_get(v___x_2955_, 5);
v_defEqI_2963_ = lean_ctor_get(v___x_2955_, 6);
v_extensions_2964_ = lean_ctor_get(v___x_2955_, 7);
v_issues_2965_ = lean_ctor_get(v___x_2955_, 8);
v_instanceOverrides_2966_ = lean_ctor_get(v___x_2955_, 10);
v_debug_2967_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*11);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2969_ = v___x_2955_;
v_isShared_2970_ = v_isSharedCheck_2988_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_instanceOverrides_2966_);
lean_inc(v_canon_2956_);
lean_inc(v_issues_2965_);
lean_inc(v_extensions_2964_);
lean_inc(v_defEqI_2963_);
lean_inc(v_congrInfo_2962_);
lean_inc(v_getLevel_2961_);
lean_inc(v_inferType_2960_);
lean_inc(v_proofInstInfo_2959_);
lean_inc(v_maxFVar_2958_);
lean_inc(v_share_2957_);
lean_dec(v___x_2955_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2988_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_cache_2971_; lean_object* v_cacheInType_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2987_; 
v_cache_2971_ = lean_ctor_get(v_canon_2956_, 0);
v_cacheInType_2972_ = lean_ctor_get(v_canon_2956_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_canon_2956_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2974_ = v_canon_2956_;
v_isShared_2975_ = v_isSharedCheck_2987_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_cacheInType_2972_);
lean_inc(v_cache_2971_);
lean_dec(v_canon_2956_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2987_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
lean_inc(v_a_2951_);
v___x_2976_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2971_, v_e_2719_, v_a_2951_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_cacheInType_2972_);
v___x_2978_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 9, v___x_2978_);
v___x_2980_ = v___x_2969_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_share_2957_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_maxFVar_2958_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_proofInstInfo_2959_);
lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_inferType_2960_);
lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_getLevel_2961_);
lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_congrInfo_2962_);
lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_defEqI_2963_);
lean_ctor_set(v_reuseFailAlloc_2985_, 7, v_extensions_2964_);
lean_ctor_set(v_reuseFailAlloc_2985_, 8, v_issues_2965_);
lean_ctor_set(v_reuseFailAlloc_2985_, 9, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2985_, 10, v_instanceOverrides_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2985_, sizeof(void*)*11, v_debug_2967_);
v___x_2980_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2981_ = lean_st_ref_set(v_a_2722_, v___x_2980_);
if (v_isShared_2954_ == 0)
{
v___x_2983_ = v___x_2953_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2951_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 4);
return v___x_2950_;
}
}
}
else
{
lean_object* v___x_2990_; lean_object* v_canon_2991_; lean_object* v_cacheInType_2992_; lean_object* v___x_2993_; 
v___x_2990_ = lean_st_ref_get(v_a_2722_);
v_canon_2991_ = lean_ctor_get(v___x_2990_, 9);
lean_inc_ref(v_canon_2991_);
lean_dec(v___x_2990_);
v_cacheInType_2992_ = lean_ctor_get(v_canon_2991_, 1);
lean_inc_ref(v_cacheInType_2992_);
lean_dec_ref(v_canon_2991_);
v___x_2993_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2992_, v_e_2719_);
lean_dec_ref(v_cacheInType_2992_);
if (lean_obj_tag(v___x_2993_) == 1)
{
lean_object* v_val_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref_known(v_e_2719_, 4);
v_val_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_val_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 0);
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_val_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v___x_3002_; 
lean_dec(v___x_2993_);
lean_inc_ref(v_e_2719_);
v___x_3002_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2937_, v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3041_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3041_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3041_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v_canon_3008_; lean_object* v_share_3009_; lean_object* v_maxFVar_3010_; lean_object* v_proofInstInfo_3011_; lean_object* v_inferType_3012_; lean_object* v_getLevel_3013_; lean_object* v_congrInfo_3014_; lean_object* v_defEqI_3015_; lean_object* v_extensions_3016_; lean_object* v_issues_3017_; lean_object* v_instanceOverrides_3018_; uint8_t v_debug_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3040_; 
v___x_3007_ = lean_st_ref_take(v_a_2722_);
v_canon_3008_ = lean_ctor_get(v___x_3007_, 9);
v_share_3009_ = lean_ctor_get(v___x_3007_, 0);
v_maxFVar_3010_ = lean_ctor_get(v___x_3007_, 1);
v_proofInstInfo_3011_ = lean_ctor_get(v___x_3007_, 2);
v_inferType_3012_ = lean_ctor_get(v___x_3007_, 3);
v_getLevel_3013_ = lean_ctor_get(v___x_3007_, 4);
v_congrInfo_3014_ = lean_ctor_get(v___x_3007_, 5);
v_defEqI_3015_ = lean_ctor_get(v___x_3007_, 6);
v_extensions_3016_ = lean_ctor_get(v___x_3007_, 7);
v_issues_3017_ = lean_ctor_get(v___x_3007_, 8);
v_instanceOverrides_3018_ = lean_ctor_get(v___x_3007_, 10);
v_debug_3019_ = lean_ctor_get_uint8(v___x_3007_, sizeof(void*)*11);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3021_ = v___x_3007_;
v_isShared_3022_ = v_isSharedCheck_3040_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_instanceOverrides_3018_);
lean_inc(v_canon_3008_);
lean_inc(v_issues_3017_);
lean_inc(v_extensions_3016_);
lean_inc(v_defEqI_3015_);
lean_inc(v_congrInfo_3014_);
lean_inc(v_getLevel_3013_);
lean_inc(v_inferType_3012_);
lean_inc(v_proofInstInfo_3011_);
lean_inc(v_maxFVar_3010_);
lean_inc(v_share_3009_);
lean_dec(v___x_3007_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3040_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_cache_3023_; lean_object* v_cacheInType_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3039_; 
v_cache_3023_ = lean_ctor_get(v_canon_3008_, 0);
v_cacheInType_3024_ = lean_ctor_get(v_canon_3008_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_canon_3008_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3026_ = v_canon_3008_;
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_cacheInType_3024_);
lean_inc(v_cache_3023_);
lean_dec(v_canon_3008_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
lean_inc(v_a_3003_);
v___x_3028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3024_, v_e_2719_, v_a_3003_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_cache_3023_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 9, v___x_3030_);
v___x_3032_ = v___x_3021_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_share_3009_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_maxFVar_3010_);
lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_proofInstInfo_3011_);
lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_inferType_3012_);
lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_getLevel_3013_);
lean_ctor_set(v_reuseFailAlloc_3037_, 5, v_congrInfo_3014_);
lean_ctor_set(v_reuseFailAlloc_3037_, 6, v_defEqI_3015_);
lean_ctor_set(v_reuseFailAlloc_3037_, 7, v_extensions_3016_);
lean_ctor_set(v_reuseFailAlloc_3037_, 8, v_issues_3017_);
lean_ctor_set(v_reuseFailAlloc_3037_, 9, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3037_, 10, v_instanceOverrides_3018_);
lean_ctor_set_uint8(v_reuseFailAlloc_3037_, sizeof(void*)*11, v_debug_3019_);
v___x_3032_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3033_ = lean_st_ref_set(v_a_2722_, v___x_3032_);
if (v_isShared_3006_ == 0)
{
v___x_3035_ = v___x_3005_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3003_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 4);
return v___x_3002_;
}
}
}
}
case 5:
{
if (v_a_2720_ == 0)
{
lean_object* v___x_3042_; lean_object* v_canon_3043_; lean_object* v_cache_3044_; lean_object* v___x_3045_; 
v___x_3042_ = lean_st_ref_get(v_a_2722_);
v_canon_3043_ = lean_ctor_get(v___x_3042_, 9);
lean_inc_ref(v_canon_3043_);
lean_dec(v___x_3042_);
v_cache_3044_ = lean_ctor_get(v_canon_3043_, 0);
lean_inc_ref(v_cache_3044_);
lean_dec_ref(v_canon_3043_);
v___x_3045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3044_, v_e_2719_);
lean_dec_ref(v_cache_3044_);
if (lean_obj_tag(v___x_3045_) == 1)
{
lean_object* v_val_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref_known(v_e_2719_, 2);
v_val_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_val_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set_tag(v___x_3048_, 0);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_val_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
else
{
lean_object* v___x_3054_; 
lean_dec(v___x_3045_);
lean_inc_ref(v_e_2719_);
v___x_3054_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3093_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3093_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3093_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v_canon_3060_; lean_object* v_share_3061_; lean_object* v_maxFVar_3062_; lean_object* v_proofInstInfo_3063_; lean_object* v_inferType_3064_; lean_object* v_getLevel_3065_; lean_object* v_congrInfo_3066_; lean_object* v_defEqI_3067_; lean_object* v_extensions_3068_; lean_object* v_issues_3069_; lean_object* v_instanceOverrides_3070_; uint8_t v_debug_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3092_; 
v___x_3059_ = lean_st_ref_take(v_a_2722_);
v_canon_3060_ = lean_ctor_get(v___x_3059_, 9);
v_share_3061_ = lean_ctor_get(v___x_3059_, 0);
v_maxFVar_3062_ = lean_ctor_get(v___x_3059_, 1);
v_proofInstInfo_3063_ = lean_ctor_get(v___x_3059_, 2);
v_inferType_3064_ = lean_ctor_get(v___x_3059_, 3);
v_getLevel_3065_ = lean_ctor_get(v___x_3059_, 4);
v_congrInfo_3066_ = lean_ctor_get(v___x_3059_, 5);
v_defEqI_3067_ = lean_ctor_get(v___x_3059_, 6);
v_extensions_3068_ = lean_ctor_get(v___x_3059_, 7);
v_issues_3069_ = lean_ctor_get(v___x_3059_, 8);
v_instanceOverrides_3070_ = lean_ctor_get(v___x_3059_, 10);
v_debug_3071_ = lean_ctor_get_uint8(v___x_3059_, sizeof(void*)*11);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3073_ = v___x_3059_;
v_isShared_3074_ = v_isSharedCheck_3092_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_instanceOverrides_3070_);
lean_inc(v_canon_3060_);
lean_inc(v_issues_3069_);
lean_inc(v_extensions_3068_);
lean_inc(v_defEqI_3067_);
lean_inc(v_congrInfo_3066_);
lean_inc(v_getLevel_3065_);
lean_inc(v_inferType_3064_);
lean_inc(v_proofInstInfo_3063_);
lean_inc(v_maxFVar_3062_);
lean_inc(v_share_3061_);
lean_dec(v___x_3059_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3092_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_cache_3075_; lean_object* v_cacheInType_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3091_; 
v_cache_3075_ = lean_ctor_get(v_canon_3060_, 0);
v_cacheInType_3076_ = lean_ctor_get(v_canon_3060_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_canon_3060_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3078_ = v_canon_3060_;
v_isShared_3079_ = v_isSharedCheck_3091_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_cacheInType_3076_);
lean_inc(v_cache_3075_);
lean_dec(v_canon_3060_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3091_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
lean_inc(v_a_3055_);
v___x_3080_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3075_, v_e_2719_, v_a_3055_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_cacheInType_3076_);
v___x_3082_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 9, v___x_3082_);
v___x_3084_ = v___x_3073_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_share_3061_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_maxFVar_3062_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_proofInstInfo_3063_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_inferType_3064_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_getLevel_3065_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_congrInfo_3066_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_defEqI_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_extensions_3068_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_issues_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3089_, 10, v_instanceOverrides_3070_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*11, v_debug_3071_);
v___x_3084_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_st_ref_set(v_a_2722_, v___x_3084_);
if (v_isShared_3058_ == 0)
{
v___x_3087_ = v___x_3057_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3055_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 2);
return v___x_3054_;
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v_canon_3095_; lean_object* v_cacheInType_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_st_ref_get(v_a_2722_);
v_canon_3095_ = lean_ctor_get(v___x_3094_, 9);
lean_inc_ref(v_canon_3095_);
lean_dec(v___x_3094_);
v_cacheInType_3096_ = lean_ctor_get(v_canon_3095_, 1);
lean_inc_ref(v_cacheInType_3096_);
lean_dec_ref(v_canon_3095_);
v___x_3097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3096_, v_e_2719_);
lean_dec_ref(v_cacheInType_3096_);
if (lean_obj_tag(v___x_3097_) == 1)
{
lean_object* v_val_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref_known(v_e_2719_, 2);
v_val_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_val_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set_tag(v___x_3100_, 0);
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_val_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
else
{
lean_object* v___x_3106_; 
lean_dec(v___x_3097_);
lean_inc_ref(v_e_2719_);
v___x_3106_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3145_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3145_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3145_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v_canon_3112_; lean_object* v_share_3113_; lean_object* v_maxFVar_3114_; lean_object* v_proofInstInfo_3115_; lean_object* v_inferType_3116_; lean_object* v_getLevel_3117_; lean_object* v_congrInfo_3118_; lean_object* v_defEqI_3119_; lean_object* v_extensions_3120_; lean_object* v_issues_3121_; lean_object* v_instanceOverrides_3122_; uint8_t v_debug_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3144_; 
v___x_3111_ = lean_st_ref_take(v_a_2722_);
v_canon_3112_ = lean_ctor_get(v___x_3111_, 9);
v_share_3113_ = lean_ctor_get(v___x_3111_, 0);
v_maxFVar_3114_ = lean_ctor_get(v___x_3111_, 1);
v_proofInstInfo_3115_ = lean_ctor_get(v___x_3111_, 2);
v_inferType_3116_ = lean_ctor_get(v___x_3111_, 3);
v_getLevel_3117_ = lean_ctor_get(v___x_3111_, 4);
v_congrInfo_3118_ = lean_ctor_get(v___x_3111_, 5);
v_defEqI_3119_ = lean_ctor_get(v___x_3111_, 6);
v_extensions_3120_ = lean_ctor_get(v___x_3111_, 7);
v_issues_3121_ = lean_ctor_get(v___x_3111_, 8);
v_instanceOverrides_3122_ = lean_ctor_get(v___x_3111_, 10);
v_debug_3123_ = lean_ctor_get_uint8(v___x_3111_, sizeof(void*)*11);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3125_ = v___x_3111_;
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_instanceOverrides_3122_);
lean_inc(v_canon_3112_);
lean_inc(v_issues_3121_);
lean_inc(v_extensions_3120_);
lean_inc(v_defEqI_3119_);
lean_inc(v_congrInfo_3118_);
lean_inc(v_getLevel_3117_);
lean_inc(v_inferType_3116_);
lean_inc(v_proofInstInfo_3115_);
lean_inc(v_maxFVar_3114_);
lean_inc(v_share_3113_);
lean_dec(v___x_3111_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_cache_3127_; lean_object* v_cacheInType_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3143_; 
v_cache_3127_ = lean_ctor_get(v_canon_3112_, 0);
v_cacheInType_3128_ = lean_ctor_get(v_canon_3112_, 1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_canon_3112_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3130_ = v_canon_3112_;
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_cacheInType_3128_);
lean_inc(v_cache_3127_);
lean_dec(v_canon_3112_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
lean_inc(v_a_3107_);
v___x_3132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3128_, v_e_2719_, v_a_3107_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_cache_3127_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 9, v___x_3134_);
v___x_3136_ = v___x_3125_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_share_3113_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_maxFVar_3114_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_proofInstInfo_3115_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v_inferType_3116_);
lean_ctor_set(v_reuseFailAlloc_3141_, 4, v_getLevel_3117_);
lean_ctor_set(v_reuseFailAlloc_3141_, 5, v_congrInfo_3118_);
lean_ctor_set(v_reuseFailAlloc_3141_, 6, v_defEqI_3119_);
lean_ctor_set(v_reuseFailAlloc_3141_, 7, v_extensions_3120_);
lean_ctor_set(v_reuseFailAlloc_3141_, 8, v_issues_3121_);
lean_ctor_set(v_reuseFailAlloc_3141_, 9, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3141_, 10, v_instanceOverrides_3122_);
lean_ctor_set_uint8(v_reuseFailAlloc_3141_, sizeof(void*)*11, v_debug_3123_);
v___x_3136_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = lean_st_ref_set(v_a_2722_, v___x_3136_);
if (v_isShared_3110_ == 0)
{
v___x_3139_ = v___x_3109_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3107_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 2);
return v___x_3106_;
}
}
}
}
case 11:
{
if (v_a_2720_ == 0)
{
lean_object* v___x_3146_; lean_object* v_canon_3147_; lean_object* v_cache_3148_; lean_object* v___x_3149_; 
v___x_3146_ = lean_st_ref_get(v_a_2722_);
v_canon_3147_ = lean_ctor_get(v___x_3146_, 9);
lean_inc_ref(v_canon_3147_);
lean_dec(v___x_3146_);
v_cache_3148_ = lean_ctor_get(v_canon_3147_, 0);
lean_inc_ref(v_cache_3148_);
lean_dec_ref(v_canon_3147_);
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3148_, v_e_2719_);
lean_dec_ref(v_cache_3148_);
if (lean_obj_tag(v___x_3149_) == 1)
{
lean_object* v_val_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_val_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 0);
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_val_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
else
{
lean_object* v___x_3158_; 
lean_dec(v___x_3149_);
lean_inc_ref(v_e_2719_);
v___x_3158_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3197_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3197_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3197_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v_canon_3164_; lean_object* v_share_3165_; lean_object* v_maxFVar_3166_; lean_object* v_proofInstInfo_3167_; lean_object* v_inferType_3168_; lean_object* v_getLevel_3169_; lean_object* v_congrInfo_3170_; lean_object* v_defEqI_3171_; lean_object* v_extensions_3172_; lean_object* v_issues_3173_; lean_object* v_instanceOverrides_3174_; uint8_t v_debug_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3196_; 
v___x_3163_ = lean_st_ref_take(v_a_2722_);
v_canon_3164_ = lean_ctor_get(v___x_3163_, 9);
v_share_3165_ = lean_ctor_get(v___x_3163_, 0);
v_maxFVar_3166_ = lean_ctor_get(v___x_3163_, 1);
v_proofInstInfo_3167_ = lean_ctor_get(v___x_3163_, 2);
v_inferType_3168_ = lean_ctor_get(v___x_3163_, 3);
v_getLevel_3169_ = lean_ctor_get(v___x_3163_, 4);
v_congrInfo_3170_ = lean_ctor_get(v___x_3163_, 5);
v_defEqI_3171_ = lean_ctor_get(v___x_3163_, 6);
v_extensions_3172_ = lean_ctor_get(v___x_3163_, 7);
v_issues_3173_ = lean_ctor_get(v___x_3163_, 8);
v_instanceOverrides_3174_ = lean_ctor_get(v___x_3163_, 10);
v_debug_3175_ = lean_ctor_get_uint8(v___x_3163_, sizeof(void*)*11);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3177_ = v___x_3163_;
v_isShared_3178_ = v_isSharedCheck_3196_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_instanceOverrides_3174_);
lean_inc(v_canon_3164_);
lean_inc(v_issues_3173_);
lean_inc(v_extensions_3172_);
lean_inc(v_defEqI_3171_);
lean_inc(v_congrInfo_3170_);
lean_inc(v_getLevel_3169_);
lean_inc(v_inferType_3168_);
lean_inc(v_proofInstInfo_3167_);
lean_inc(v_maxFVar_3166_);
lean_inc(v_share_3165_);
lean_dec(v___x_3163_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3196_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_cache_3179_; lean_object* v_cacheInType_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3195_; 
v_cache_3179_ = lean_ctor_get(v_canon_3164_, 0);
v_cacheInType_3180_ = lean_ctor_get(v_canon_3164_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_canon_3164_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3182_ = v_canon_3164_;
v_isShared_3183_ = v_isSharedCheck_3195_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_cacheInType_3180_);
lean_inc(v_cache_3179_);
lean_dec(v_canon_3164_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3195_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
lean_inc(v_a_3159_);
v___x_3184_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3179_, v_e_2719_, v_a_3159_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3184_);
v___x_3186_ = v___x_3182_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_cacheInType_3180_);
v___x_3186_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3188_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 9, v___x_3186_);
v___x_3188_ = v___x_3177_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_share_3165_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_maxFVar_3166_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_proofInstInfo_3167_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_inferType_3168_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_getLevel_3169_);
lean_ctor_set(v_reuseFailAlloc_3193_, 5, v_congrInfo_3170_);
lean_ctor_set(v_reuseFailAlloc_3193_, 6, v_defEqI_3171_);
lean_ctor_set(v_reuseFailAlloc_3193_, 7, v_extensions_3172_);
lean_ctor_set(v_reuseFailAlloc_3193_, 8, v_issues_3173_);
lean_ctor_set(v_reuseFailAlloc_3193_, 9, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3193_, 10, v_instanceOverrides_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, sizeof(void*)*11, v_debug_3175_);
v___x_3188_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_st_ref_set(v_a_2722_, v___x_3188_);
if (v_isShared_3162_ == 0)
{
v___x_3191_ = v___x_3161_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3159_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_3158_;
}
}
}
else
{
lean_object* v___x_3198_; lean_object* v_canon_3199_; lean_object* v_cacheInType_3200_; lean_object* v___x_3201_; 
v___x_3198_ = lean_st_ref_get(v_a_2722_);
v_canon_3199_ = lean_ctor_get(v___x_3198_, 9);
lean_inc_ref(v_canon_3199_);
lean_dec(v___x_3198_);
v_cacheInType_3200_ = lean_ctor_get(v_canon_3199_, 1);
lean_inc_ref(v_cacheInType_3200_);
lean_dec_ref(v_canon_3199_);
v___x_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3200_, v_e_2719_);
lean_dec_ref(v_cacheInType_3200_);
if (lean_obj_tag(v___x_3201_) == 1)
{
lean_object* v_val_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref_known(v_e_2719_, 3);
v_val_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_val_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 0);
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_val_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
else
{
lean_object* v___x_3210_; 
lean_dec(v___x_3201_);
lean_inc_ref(v_e_2719_);
v___x_3210_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3249_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3249_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3249_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v_canon_3216_; lean_object* v_share_3217_; lean_object* v_maxFVar_3218_; lean_object* v_proofInstInfo_3219_; lean_object* v_inferType_3220_; lean_object* v_getLevel_3221_; lean_object* v_congrInfo_3222_; lean_object* v_defEqI_3223_; lean_object* v_extensions_3224_; lean_object* v_issues_3225_; lean_object* v_instanceOverrides_3226_; uint8_t v_debug_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3248_; 
v___x_3215_ = lean_st_ref_take(v_a_2722_);
v_canon_3216_ = lean_ctor_get(v___x_3215_, 9);
v_share_3217_ = lean_ctor_get(v___x_3215_, 0);
v_maxFVar_3218_ = lean_ctor_get(v___x_3215_, 1);
v_proofInstInfo_3219_ = lean_ctor_get(v___x_3215_, 2);
v_inferType_3220_ = lean_ctor_get(v___x_3215_, 3);
v_getLevel_3221_ = lean_ctor_get(v___x_3215_, 4);
v_congrInfo_3222_ = lean_ctor_get(v___x_3215_, 5);
v_defEqI_3223_ = lean_ctor_get(v___x_3215_, 6);
v_extensions_3224_ = lean_ctor_get(v___x_3215_, 7);
v_issues_3225_ = lean_ctor_get(v___x_3215_, 8);
v_instanceOverrides_3226_ = lean_ctor_get(v___x_3215_, 10);
v_debug_3227_ = lean_ctor_get_uint8(v___x_3215_, sizeof(void*)*11);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3229_ = v___x_3215_;
v_isShared_3230_ = v_isSharedCheck_3248_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_instanceOverrides_3226_);
lean_inc(v_canon_3216_);
lean_inc(v_issues_3225_);
lean_inc(v_extensions_3224_);
lean_inc(v_defEqI_3223_);
lean_inc(v_congrInfo_3222_);
lean_inc(v_getLevel_3221_);
lean_inc(v_inferType_3220_);
lean_inc(v_proofInstInfo_3219_);
lean_inc(v_maxFVar_3218_);
lean_inc(v_share_3217_);
lean_dec(v___x_3215_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3248_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_cache_3231_; lean_object* v_cacheInType_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3247_; 
v_cache_3231_ = lean_ctor_get(v_canon_3216_, 0);
v_cacheInType_3232_ = lean_ctor_get(v_canon_3216_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_canon_3216_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3234_ = v_canon_3216_;
v_isShared_3235_ = v_isSharedCheck_3247_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_cacheInType_3232_);
lean_inc(v_cache_3231_);
lean_dec(v_canon_3216_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3247_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_inc(v_a_3211_);
v___x_3236_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3232_, v_e_2719_, v_a_3211_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_cache_3231_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 9, v___x_3238_);
v___x_3240_ = v___x_3229_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_share_3217_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_maxFVar_3218_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_proofInstInfo_3219_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_inferType_3220_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v_getLevel_3221_);
lean_ctor_set(v_reuseFailAlloc_3245_, 5, v_congrInfo_3222_);
lean_ctor_set(v_reuseFailAlloc_3245_, 6, v_defEqI_3223_);
lean_ctor_set(v_reuseFailAlloc_3245_, 7, v_extensions_3224_);
lean_ctor_set(v_reuseFailAlloc_3245_, 8, v_issues_3225_);
lean_ctor_set(v_reuseFailAlloc_3245_, 9, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3245_, 10, v_instanceOverrides_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3245_, sizeof(void*)*11, v_debug_3227_);
v___x_3240_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3241_ = lean_st_ref_set(v_a_2722_, v___x_3240_);
if (v_isShared_3214_ == 0)
{
v___x_3243_ = v___x_3213_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3211_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2719_, 3);
return v___x_3210_;
}
}
}
}
case 10:
{
lean_object* v_data_3250_; lean_object* v_expr_3251_; lean_object* v___x_3252_; 
v_data_3250_ = lean_ctor_get(v_e_2719_, 0);
v_expr_3251_ = lean_ctor_get(v_e_2719_, 1);
lean_inc_ref(v_expr_3251_);
v___x_3252_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3251_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3267_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3267_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3267_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
size_t v___x_3257_; size_t v___x_3258_; uint8_t v___x_3259_; 
v___x_3257_ = lean_ptr_addr(v_expr_3251_);
v___x_3258_ = lean_ptr_addr(v_a_3253_);
v___x_3259_ = lean_usize_dec_eq(v___x_3257_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_inc(v_data_3250_);
lean_dec_ref_known(v_e_2719_, 2);
v___x_3260_ = l_Lean_Expr_mdata___override(v_data_3250_, v_a_3253_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3260_);
v___x_3262_ = v___x_3255_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
else
{
lean_object* v___x_3265_; 
lean_dec(v_a_3253_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v_e_2719_);
v___x_3265_ = v___x_3255_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_e_2719_);
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
else
{
lean_dec_ref_known(v_e_2719_, 2);
return v___x_3252_;
}
}
default: 
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_e_2719_);
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3269_, uint8_t v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
if (v_a_3270_ == 0)
{
lean_object* v___x_3278_; 
lean_inc_ref(v_e_3269_);
v___x_3278_ = l_Lean_Meta_isProp(v_e_3269_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
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
uint8_t v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = 1;
v___x_3282_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3269_, v___x_3281_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3283_;
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v_e_3269_);
v_a_3284_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3278_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3278_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3293_, lean_object* v_body_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v___y_67153__boxed_3304_; lean_object* v_res_3305_; 
v___y_67153__boxed_3304_ = lean_unbox(v___y_3296_);
v_res_3305_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3293_, v_body_3294_, v_x_3295_, v___y_67153__boxed_3304_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3306_, lean_object* v_e_3307_, uint8_t v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
if (lean_obj_tag(v_e_3307_) == 7)
{
lean_object* v_binderName_3316_; lean_object* v_binderType_3317_; lean_object* v_body_3318_; uint8_t v_binderInfo_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_binderName_3316_ = lean_ctor_get(v_e_3307_, 0);
lean_inc(v_binderName_3316_);
v_binderType_3317_ = lean_ctor_get(v_e_3307_, 1);
lean_inc_ref(v_binderType_3317_);
v_body_3318_ = lean_ctor_get(v_e_3307_, 2);
lean_inc_ref(v_body_3318_);
v_binderInfo_3319_ = lean_ctor_get_uint8(v_e_3307_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3307_, 3);
v___x_3320_ = lean_expr_instantiate_rev(v_binderType_3317_, v_fvars_3306_);
lean_dec_ref(v_binderType_3317_);
v___x_3321_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3320_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___f_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3323_, 0, v_fvars_3306_);
lean_closure_set(v___f_3323_, 1, v_body_3318_);
v___x_3324_ = 0;
v___x_3325_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3316_, v_binderInfo_3319_, v_a_3322_, v___f_3323_, v___x_3324_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3325_;
}
else
{
lean_dec_ref(v_body_3318_);
lean_dec(v_binderName_3316_);
lean_dec_ref(v_fvars_3306_);
return v___x_3321_;
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_expr_instantiate_rev(v_e_3307_, v_fvars_3306_);
lean_dec_ref(v_e_3307_);
v___x_3327_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3326_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = 0;
v___x_3330_ = 1;
v___x_3331_ = 1;
v___x_3332_ = l_Lean_Meta_mkForallFVars(v_fvars_3306_, v_a_3328_, v___x_3329_, v___x_3330_, v___x_3330_, v___x_3331_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec_ref(v_fvars_3306_);
return v___x_3332_;
}
else
{
lean_dec_ref(v_fvars_3306_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3333_, lean_object* v_body_3334_, lean_object* v_x_3335_, uint8_t v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_array_push(v_fvars_3333_, v_x_3335_);
v___x_3345_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3344_, v_body_3334_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
uint8_t v_a_boxed_3355_; lean_object* v_res_3356_; 
v_a_boxed_3355_ = lean_unbox(v_a_3347_);
v_res_3356_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3346_, v_a_boxed_3355_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
uint8_t v_a_boxed_3366_; lean_object* v_res_3367_; 
v_a_boxed_3366_ = lean_unbox(v_a_3358_);
v_res_3367_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3357_, v_a_boxed_3366_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
uint8_t v_a_boxed_3377_; lean_object* v_res_3378_; 
v_a_boxed_3377_ = lean_unbox(v_a_3369_);
v_res_3378_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3368_, v_a_boxed_3377_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
uint8_t v_a_boxed_3388_; lean_object* v_res_3389_; 
v_a_boxed_3388_ = lean_unbox(v_a_3380_);
v_res_3389_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3379_, v_a_boxed_3388_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
uint8_t v_a_boxed_3399_; lean_object* v_res_3400_; 
v_a_boxed_3399_ = lean_unbox(v_a_3391_);
v_res_3400_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3390_, v_a_boxed_3399_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3401_, lean_object* v_e_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
uint8_t v_a_boxed_3411_; lean_object* v_res_3412_; 
v_a_boxed_3411_ = lean_unbox(v_a_3403_);
v_res_3412_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3401_, v_e_3402_, v_a_boxed_3411_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3413_, lean_object* v_e_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
uint8_t v_a_boxed_3423_; lean_object* v_res_3424_; 
v_a_boxed_3423_ = lean_unbox(v_a_3415_);
v_res_3424_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3413_, v_e_3414_, v_a_boxed_3423_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3425_, lean_object* v_report_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_){
_start:
{
uint8_t v_report_boxed_3435_; uint8_t v_a_boxed_3436_; lean_object* v_res_3437_; 
v_report_boxed_3435_ = lean_unbox(v_report_3426_);
v_a_boxed_3436_ = lean_unbox(v_a_3427_);
v_res_3437_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3425_, v_report_boxed_3435_, v_a_boxed_3436_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
uint8_t v_a_boxed_3447_; lean_object* v_res_3448_; 
v_a_boxed_3447_ = lean_unbox(v_a_3439_);
v_res_3448_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3438_, v_a_boxed_3447_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3449_, lean_object* v_e_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
uint8_t v_a_boxed_3459_; lean_object* v_res_3460_; 
v_a_boxed_3459_ = lean_unbox(v_a_3451_);
v_res_3460_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3449_, v_e_3450_, v_a_boxed_3459_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3461_, lean_object* v_00_u03b1_3462_, lean_object* v_c_3463_, lean_object* v_a_3464_, lean_object* v_b_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
uint8_t v_a_boxed_3474_; lean_object* v_res_3475_; 
v_a_boxed_3474_ = lean_unbox(v_a_3466_);
v_res_3475_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3461_, v_00_u03b1_3462_, v_c_3463_, v_a_3464_, v_b_3465_, v_a_boxed_3474_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3476_, lean_object* v_00_u03b1_3477_, lean_object* v_c_3478_, lean_object* v_inst_3479_, lean_object* v_a_3480_, lean_object* v_b_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
uint8_t v_a_boxed_3490_; lean_object* v_res_3491_; 
v_a_boxed_3490_ = lean_unbox(v_a_3482_);
v_res_3491_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3476_, v_00_u03b1_3477_, v_c_3478_, v_inst_3479_, v_a_3480_, v_b_3481_, v_a_boxed_3490_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
uint8_t v_a_boxed_3501_; lean_object* v_res_3502_; 
v_a_boxed_3501_ = lean_unbox(v_a_3493_);
v_res_3502_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3492_, v_a_boxed_3501_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
uint8_t v_a_boxed_3512_; lean_object* v_res_3513_; 
v_a_boxed_3512_ = lean_unbox(v_a_3504_);
v_res_3513_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3503_, v_a_boxed_3512_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3514_, lean_object* v_prop_3515_, lean_object* v_inst_3516_, lean_object* v_e_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
uint8_t v_a_boxed_3526_; lean_object* v_res_3527_; 
v_a_boxed_3526_ = lean_unbox(v_a_3518_);
v_res_3527_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3514_, v_prop_3515_, v_inst_3516_, v_e_3517_, v_a_boxed_3526_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3528_, lean_object* v_report_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
uint8_t v_report_boxed_3538_; uint8_t v_a_boxed_3539_; lean_object* v_res_3540_; 
v_report_boxed_3538_ = lean_unbox(v_report_3529_);
v_a_boxed_3539_ = lean_unbox(v_a_3530_);
v_res_3540_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3528_, v_report_boxed_3538_, v_a_boxed_3539_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3541_, lean_object* v_prop_3542_, lean_object* v_h_3543_, lean_object* v_e_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
uint8_t v_a_boxed_3553_; lean_object* v_res_3554_; 
v_a_boxed_3553_ = lean_unbox(v_a_3545_);
v_res_3554_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3541_, v_prop_3542_, v_h_3543_, v_e_3544_, v_a_boxed_3553_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
uint8_t v_a_boxed_3564_; lean_object* v_res_3565_; 
v_a_boxed_3564_ = lean_unbox(v_a_3556_);
v_res_3565_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3555_, v_a_boxed_3564_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3566_, lean_object* v___x_3567_, lean_object* v_a_3568_, lean_object* v_b_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
uint8_t v___y_67580__boxed_3578_; lean_object* v_res_3579_; 
v___y_67580__boxed_3578_ = lean_unbox(v___y_3570_);
v_res_3579_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3566_, v___x_3567_, v_a_3568_, v_b_3569_, v___y_67580__boxed_3578_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___x_3567_);
lean_dec(v_upperBound_3566_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3580_, lean_object* v_a_3581_, lean_object* v___x_3582_, lean_object* v_snd_3583_, lean_object* v___x_3584_, lean_object* v_fst_3585_, lean_object* v_____r_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
uint8_t v___x_67645__boxed_3595_; uint8_t v___y_67647__boxed_3596_; lean_object* v_res_3597_; 
v___x_67645__boxed_3595_ = lean_unbox(v___x_3584_);
v___y_67647__boxed_3596_ = lean_unbox(v___y_3587_);
v_res_3597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3580_, v_a_3581_, v___x_3582_, v_snd_3583_, v___x_67645__boxed_3595_, v_fst_3585_, v_____r_3586_, v___y_67647__boxed_3596_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v_a_3581_);
lean_dec_ref(v___x_3580_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3598_, lean_object* v_prop_3599_, lean_object* v_h_3600_, lean_object* v_e_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
uint8_t v_a_boxed_3610_; lean_object* v_res_3611_; 
v_a_boxed_3610_ = lean_unbox(v_a_3602_);
v_res_3611_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3598_, v_prop_3599_, v_h_3600_, v_e_3601_, v_a_boxed_3610_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
uint8_t v___y_67771__boxed_3624_; lean_object* v_res_3625_; 
v___y_67771__boxed_3624_ = lean_unbox(v___y_3616_);
v_res_3625_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3612_, v_x_3613_, v_x_3614_, v_x_3615_, v___y_67771__boxed_3624_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
uint8_t v_a_boxed_3635_; lean_object* v_res_3636_; 
v_a_boxed_3635_ = lean_unbox(v_a_3627_);
v_res_3636_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3626_, v_a_boxed_3635_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3637_, uint8_t v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3637_, v___y_3644_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v___y_70109__boxed_3656_; lean_object* v_res_3657_; 
v___y_70109__boxed_3656_ = lean_unbox(v___y_3648_);
v_res_3657_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3647_, v___y_70109__boxed_3656_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3658_, lean_object* v_name_3659_, lean_object* v_type_3660_, lean_object* v_val_3661_, lean_object* v_k_3662_, uint8_t v_nondep_3663_, uint8_t v_kind_3664_, uint8_t v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3659_, v_type_3660_, v_val_3661_, v_k_3662_, v_nondep_3663_, v_kind_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3674_, lean_object* v_name_3675_, lean_object* v_type_3676_, lean_object* v_val_3677_, lean_object* v_k_3678_, lean_object* v_nondep_3679_, lean_object* v_kind_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_nondep_boxed_3689_; uint8_t v_kind_boxed_3690_; uint8_t v___y_70135__boxed_3691_; lean_object* v_res_3692_; 
v_nondep_boxed_3689_ = lean_unbox(v_nondep_3679_);
v_kind_boxed_3690_ = lean_unbox(v_kind_3680_);
v___y_70135__boxed_3691_ = lean_unbox(v___y_3681_);
v_res_3692_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3674_, v_name_3675_, v_type_3676_, v_val_3677_, v_k_3678_, v_nondep_boxed_3689_, v_kind_boxed_3690_, v___y_70135__boxed_3691_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3693_, lean_object* v_name_3694_, uint8_t v_bi_3695_, lean_object* v_type_3696_, lean_object* v_k_3697_, uint8_t v_kind_3698_, uint8_t v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3694_, v_bi_3695_, v_type_3696_, v_k_3697_, v_kind_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_name_3709_, lean_object* v_bi_3710_, lean_object* v_type_3711_, lean_object* v_k_3712_, lean_object* v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
uint8_t v_bi_boxed_3722_; uint8_t v_kind_boxed_3723_; uint8_t v___y_70161__boxed_3724_; lean_object* v_res_3725_; 
v_bi_boxed_3722_ = lean_unbox(v_bi_3710_);
v_kind_boxed_3723_ = lean_unbox(v_kind_3713_);
v___y_70161__boxed_3724_ = lean_unbox(v___y_3714_);
v_res_3725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3708_, v_name_3709_, v_bi_boxed_3722_, v_type_3711_, v_k_3712_, v_kind_boxed_3723_, v___y_70161__boxed_3724_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3726_, lean_object* v_m_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3727_, v_a_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3730_, lean_object* v_m_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3730_, v_m_3731_, v_a_3732_);
lean_dec_ref(v_a_3732_);
lean_dec_ref(v_m_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3734_, lean_object* v_m_3735_, lean_object* v_a_3736_, lean_object* v_b_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3735_, v_a_3736_, v_b_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3739_, lean_object* v_msg_3740_, uint8_t v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3739_, v_msg_3740_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3750_, lean_object* v_msg_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v___y_70191__boxed_3760_; lean_object* v_res_3761_; 
v___y_70191__boxed_3760_ = lean_unbox(v___y_3752_);
v_res_3761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3750_, v_msg_3751_, v___y_70191__boxed_3760_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3762_, lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v_inst_3765_, lean_object* v_R_3766_, lean_object* v_a_3767_, lean_object* v_b_3768_, lean_object* v_c_3769_, uint8_t v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3762_, v___x_3764_, v_a_3767_, v_b_3768_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3779_, lean_object* v___x_3780_, lean_object* v___x_3781_, lean_object* v_inst_3782_, lean_object* v_R_3783_, lean_object* v_a_3784_, lean_object* v_b_3785_, lean_object* v_c_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
uint8_t v___y_70221__boxed_3795_; lean_object* v_res_3796_; 
v___y_70221__boxed_3795_ = lean_unbox(v___y_3787_);
v_res_3796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3779_, v___x_3780_, v___x_3781_, v_inst_3782_, v_R_3783_, v_a_3784_, v_b_3785_, v_c_3786_, v___y_70221__boxed_3795_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v___x_3781_);
lean_dec(v___x_3780_);
lean_dec(v_upperBound_3779_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3797_, lean_object* v_a_3798_, lean_object* v_x_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3798_, v_x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3801_, lean_object* v_a_3802_, lean_object* v_x_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3801_, v_a_3802_, v_x_3803_);
lean_dec(v_x_3803_);
lean_dec_ref(v_a_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3805_, lean_object* v_a_3806_, lean_object* v_x_3807_){
_start:
{
uint8_t v___x_3808_; 
v___x_3808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3806_, v_x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3809_, lean_object* v_a_3810_, lean_object* v_x_3811_){
_start:
{
uint8_t v_res_3812_; lean_object* v_r_3813_; 
v_res_3812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3809_, v_a_3810_, v_x_3811_);
lean_dec(v_x_3811_);
lean_dec_ref(v_a_3810_);
v_r_3813_ = lean_box(v_res_3812_);
return v_r_3813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3814_, lean_object* v_data_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3817_, lean_object* v_a_3818_, lean_object* v_b_3819_, lean_object* v_x_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3818_, v_b_3819_, v_x_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3822_, lean_object* v_i_3823_, lean_object* v_source_3824_, lean_object* v_target_3825_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3823_, v_source_3824_, v_target_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3827_, lean_object* v_x_3828_, lean_object* v_x_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3828_, v_x_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3831_, lean_object* v_i_3832_, lean_object* v_arg_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3831_, v_i_3832_, v_arg_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3855_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3855_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3855_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_unbox(v_a_3840_);
lean_dec(v_a_3840_);
if (v___x_3844_ == 3)
{
uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3845_ = 0;
v___x_3846_ = lean_box(v___x_3845_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3846_);
v___x_3848_ = v___x_3842_;
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
else
{
uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3850_ = 1;
v___x_3851_ = lean_box(v___x_3850_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3851_);
v___x_3853_ = v___x_3842_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
v_a_3856_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3839_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3839_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3864_, lean_object* v_i_3865_, lean_object* v_arg_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3864_, v_i_3865_, v_arg_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_i_3865_);
lean_dec_ref(v_pinfos_3864_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3873_, lean_object* v_opts_3874_, lean_object* v_act_3875_, lean_object* v_decl_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
v___x_3884_ = lean_apply_6(v_act_3875_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
v___x_3885_ = l_Lean_profileitIOUnsafe___redArg(v_category_3873_, v_opts_3874_, v___x_3884_, v_decl_3876_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3886_, lean_object* v_opts_3887_, lean_object* v_act_3888_, lean_object* v_decl_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3886_, v_opts_3887_, v_act_3888_, v_decl_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v_opts_3887_);
lean_dec_ref(v_category_3886_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3898_, lean_object* v_category_3899_, lean_object* v_opts_3900_, lean_object* v_act_3901_, lean_object* v_decl_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3899_, v_opts_3900_, v_act_3901_, v_decl_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3911_, lean_object* v_category_3912_, lean_object* v_opts_3913_, lean_object* v_act_3914_, lean_object* v_decl_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3911_, v_category_3912_, v_opts_3913_, v_act_3914_, v_decl_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v_opts_3913_);
lean_dec_ref(v_category_3912_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3924_, lean_object* v_e_3925_, uint8_t v___x_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_keyedConfig_3934_; uint8_t v_trackZetaDelta_3935_; lean_object* v_zetaDeltaSet_3936_; lean_object* v_lctx_3937_; lean_object* v_localInstances_3938_; lean_object* v_defEqCtx_x3f_3939_; lean_object* v_synthPendingDepth_3940_; lean_object* v_customCanUnfoldPredicate_x3f_3941_; uint8_t v_univApprox_3942_; uint8_t v_inTypeClassResolution_3943_; uint8_t v_cacheInferType_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_keyedConfig_3934_ = lean_ctor_get(v___y_3929_, 0);
v_trackZetaDelta_3935_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*7);
v_zetaDeltaSet_3936_ = lean_ctor_get(v___y_3929_, 1);
v_lctx_3937_ = lean_ctor_get(v___y_3929_, 2);
v_localInstances_3938_ = lean_ctor_get(v___y_3929_, 3);
v_defEqCtx_x3f_3939_ = lean_ctor_get(v___y_3929_, 4);
v_synthPendingDepth_3940_ = lean_ctor_get(v___y_3929_, 5);
v_customCanUnfoldPredicate_x3f_3941_ = lean_ctor_get(v___y_3929_, 6);
v_univApprox_3942_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3943_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*7 + 2);
v_cacheInferType_3944_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3934_);
v___x_3945_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3924_, v_keyedConfig_3934_);
lean_inc(v_customCanUnfoldPredicate_x3f_3941_);
lean_inc(v_synthPendingDepth_3940_);
lean_inc(v_defEqCtx_x3f_3939_);
lean_inc_ref(v_localInstances_3938_);
lean_inc_ref(v_lctx_3937_);
lean_inc(v_zetaDeltaSet_3936_);
v___x_3946_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v_zetaDeltaSet_3936_);
lean_ctor_set(v___x_3946_, 2, v_lctx_3937_);
lean_ctor_set(v___x_3946_, 3, v_localInstances_3938_);
lean_ctor_set(v___x_3946_, 4, v_defEqCtx_x3f_3939_);
lean_ctor_set(v___x_3946_, 5, v_synthPendingDepth_3940_);
lean_ctor_set(v___x_3946_, 6, v_customCanUnfoldPredicate_x3f_3941_);
lean_ctor_set_uint8(v___x_3946_, sizeof(void*)*7, v_trackZetaDelta_3935_);
lean_ctor_set_uint8(v___x_3946_, sizeof(void*)*7 + 1, v_univApprox_3942_);
lean_ctor_set_uint8(v___x_3946_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3943_);
lean_ctor_set_uint8(v___x_3946_, sizeof(void*)*7 + 3, v_cacheInferType_3944_);
v___x_3947_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3925_, v___x_3926_, v___y_3927_, v___y_3928_, v___x_3946_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec_ref_known(v___x_3946_, 7);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3948_, lean_object* v_e_3949_, lean_object* v___x_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v___x_1951__boxed_3958_; uint8_t v___x_1952__boxed_3959_; lean_object* v_res_3960_; 
v___x_1951__boxed_3958_ = lean_unbox(v___x_3948_);
v___x_1952__boxed_3959_ = lean_unbox(v___x_3950_);
v_res_3960_ = l_Lean_Meta_Sym_canon___lam__0(v___x_1951__boxed_3958_, v_e_3949_, v___x_1952__boxed_3959_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v_options_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___f_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_options_3970_ = lean_ctor_get(v_a_3967_, 2);
v___x_3971_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3972_ = 0;
v___x_3973_ = 2;
v___x_3974_ = lean_box(v___x_3973_);
v___x_3975_ = lean_box(v___x_3972_);
v___f_3976_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3976_, 0, v___x_3974_);
lean_closure_set(v___f_3976_, 1, v_e_3962_);
lean_closure_set(v___f_3976_, 2, v___x_3975_);
v___x_3977_ = lean_box(0);
v___x_3978_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3971_, v_options_3970_, v___f_3976_, v___x_3977_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_Sym_canon(v_e_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3987_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

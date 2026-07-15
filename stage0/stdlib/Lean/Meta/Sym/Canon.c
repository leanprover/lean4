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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_64850__boxed_1213_; lean_object* v_res_1214_; 
v___y_64850__boxed_1213_ = lean_unbox(v___y_1204_);
v_res_1214_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1203_, v___y_64850__boxed_1213_, v___y_1205_, v___y_1206_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
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
uint8_t v_bi_boxed_1252_; uint8_t v_kind_boxed_1253_; uint8_t v___y_64878__boxed_1254_; lean_object* v_res_1255_; 
v_bi_boxed_1252_ = lean_unbox(v_bi_1240_);
v_kind_boxed_1253_ = lean_unbox(v_kind_1243_);
v___y_64878__boxed_1254_ = lean_unbox(v___y_1244_);
v_res_1255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1239_, v_bi_boxed_1252_, v_type_1241_, v_k_1242_, v_kind_boxed_1253_, v___y_64878__boxed_1254_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
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
uint8_t v_nondep_boxed_1429_; uint8_t v_kind_boxed_1430_; uint8_t v___y_65113__boxed_1431_; lean_object* v_res_1432_; 
v_nondep_boxed_1429_ = lean_unbox(v_nondep_1419_);
v_kind_boxed_1430_ = lean_unbox(v_kind_1420_);
v___y_65113__boxed_1431_ = lean_unbox(v___y_1421_);
v_res_1432_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1415_, v_type_1416_, v_val_1417_, v_k_1418_, v_nondep_boxed_1429_, v_kind_boxed_1430_, v___y_65113__boxed_1431_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
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
uint8_t v___y_65276__boxed_1462_; lean_object* v_res_1463_; 
v___y_65276__boxed_1462_ = lean_unbox(v___y_1454_);
v_res_1463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1451_, v_body_1452_, v_x_1453_, v___y_65276__boxed_1462_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
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
uint8_t v___y_65287__boxed_1529_; lean_object* v_res_1530_; 
v___y_65287__boxed_1529_ = lean_unbox(v___y_1521_);
v_res_1530_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1518_, v_body_1519_, v_x_1520_, v___y_65287__boxed_1529_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
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
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1585_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1574_, v_a_1587_, v_report_1575_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1588_;
}
else
{
lean_dec_ref(v_e_1574_);
return v___x_1586_;
}
}
else
{
lean_dec_ref(v_e_1574_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1589_, uint8_t v_report_1590_, uint8_t v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
if (v_a_1591_ == 0)
{
lean_object* v___x_1599_; lean_object* v_canon_1600_; lean_object* v_cache_1601_; lean_object* v___x_1602_; 
v___x_1599_ = lean_st_ref_get(v_a_1593_);
v_canon_1600_ = lean_ctor_get(v___x_1599_, 9);
lean_inc_ref(v_canon_1600_);
lean_dec(v___x_1599_);
v_cache_1601_ = lean_ctor_get(v_canon_1600_, 0);
lean_inc_ref(v_cache_1601_);
lean_dec_ref(v_canon_1600_);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1601_, v_e_1589_);
lean_dec_ref(v_cache_1601_);
if (lean_obj_tag(v___x_1602_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_e_1589_);
v_val_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_val_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 0);
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_val_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v___x_1611_; 
lean_dec(v___x_1602_);
lean_inc_ref(v_e_1589_);
v___x_1611_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1589_, v_report_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1650_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1650_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1650_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v_canon_1617_; lean_object* v_share_1618_; lean_object* v_maxFVar_1619_; lean_object* v_proofInstInfo_1620_; lean_object* v_inferType_1621_; lean_object* v_getLevel_1622_; lean_object* v_congrInfo_1623_; lean_object* v_defEqI_1624_; lean_object* v_extensions_1625_; lean_object* v_issues_1626_; lean_object* v_instanceOverrides_1627_; uint8_t v_debug_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1649_; 
v___x_1616_ = lean_st_ref_take(v_a_1593_);
v_canon_1617_ = lean_ctor_get(v___x_1616_, 9);
v_share_1618_ = lean_ctor_get(v___x_1616_, 0);
v_maxFVar_1619_ = lean_ctor_get(v___x_1616_, 1);
v_proofInstInfo_1620_ = lean_ctor_get(v___x_1616_, 2);
v_inferType_1621_ = lean_ctor_get(v___x_1616_, 3);
v_getLevel_1622_ = lean_ctor_get(v___x_1616_, 4);
v_congrInfo_1623_ = lean_ctor_get(v___x_1616_, 5);
v_defEqI_1624_ = lean_ctor_get(v___x_1616_, 6);
v_extensions_1625_ = lean_ctor_get(v___x_1616_, 7);
v_issues_1626_ = lean_ctor_get(v___x_1616_, 8);
v_instanceOverrides_1627_ = lean_ctor_get(v___x_1616_, 10);
v_debug_1628_ = lean_ctor_get_uint8(v___x_1616_, sizeof(void*)*11);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1630_ = v___x_1616_;
v_isShared_1631_ = v_isSharedCheck_1649_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_instanceOverrides_1627_);
lean_inc(v_canon_1617_);
lean_inc(v_issues_1626_);
lean_inc(v_extensions_1625_);
lean_inc(v_defEqI_1624_);
lean_inc(v_congrInfo_1623_);
lean_inc(v_getLevel_1622_);
lean_inc(v_inferType_1621_);
lean_inc(v_proofInstInfo_1620_);
lean_inc(v_maxFVar_1619_);
lean_inc(v_share_1618_);
lean_dec(v___x_1616_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1649_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_cache_1632_; lean_object* v_cacheInType_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1648_; 
v_cache_1632_ = lean_ctor_get(v_canon_1617_, 0);
v_cacheInType_1633_ = lean_ctor_get(v_canon_1617_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_canon_1617_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1635_ = v_canon_1617_;
v_isShared_1636_ = v_isSharedCheck_1648_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_cacheInType_1633_);
lean_inc(v_cache_1632_);
lean_dec(v_canon_1617_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1648_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_inc(v_a_1612_);
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1632_, v_e_1589_, v_a_1612_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_cacheInType_1633_);
v___x_1639_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 9, v___x_1639_);
v___x_1641_ = v___x_1630_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_share_1618_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_maxFVar_1619_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_proofInstInfo_1620_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_inferType_1621_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_getLevel_1622_);
lean_ctor_set(v_reuseFailAlloc_1646_, 5, v_congrInfo_1623_);
lean_ctor_set(v_reuseFailAlloc_1646_, 6, v_defEqI_1624_);
lean_ctor_set(v_reuseFailAlloc_1646_, 7, v_extensions_1625_);
lean_ctor_set(v_reuseFailAlloc_1646_, 8, v_issues_1626_);
lean_ctor_set(v_reuseFailAlloc_1646_, 9, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1646_, 10, v_instanceOverrides_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*11, v_debug_1628_);
v___x_1641_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_st_ref_set(v_a_1593_, v___x_1641_);
if (v_isShared_1615_ == 0)
{
v___x_1644_ = v___x_1614_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1612_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1589_);
return v___x_1611_;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v_canon_1652_; lean_object* v_cacheInType_1653_; lean_object* v___x_1654_; 
v___x_1651_ = lean_st_ref_get(v_a_1593_);
v_canon_1652_ = lean_ctor_get(v___x_1651_, 9);
lean_inc_ref(v_canon_1652_);
lean_dec(v___x_1651_);
v_cacheInType_1653_ = lean_ctor_get(v_canon_1652_, 1);
lean_inc_ref(v_cacheInType_1653_);
lean_dec_ref(v_canon_1652_);
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1653_, v_e_1589_);
lean_dec_ref(v_cacheInType_1653_);
if (lean_obj_tag(v___x_1654_) == 1)
{
lean_object* v_val_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v_e_1589_);
v_val_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_val_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 0);
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_val_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v___x_1663_; 
lean_dec(v___x_1654_);
lean_inc_ref(v_e_1589_);
v___x_1663_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1589_, v_report_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1702_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1702_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1702_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v_canon_1669_; lean_object* v_share_1670_; lean_object* v_maxFVar_1671_; lean_object* v_proofInstInfo_1672_; lean_object* v_inferType_1673_; lean_object* v_getLevel_1674_; lean_object* v_congrInfo_1675_; lean_object* v_defEqI_1676_; lean_object* v_extensions_1677_; lean_object* v_issues_1678_; lean_object* v_instanceOverrides_1679_; uint8_t v_debug_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1701_; 
v___x_1668_ = lean_st_ref_take(v_a_1593_);
v_canon_1669_ = lean_ctor_get(v___x_1668_, 9);
v_share_1670_ = lean_ctor_get(v___x_1668_, 0);
v_maxFVar_1671_ = lean_ctor_get(v___x_1668_, 1);
v_proofInstInfo_1672_ = lean_ctor_get(v___x_1668_, 2);
v_inferType_1673_ = lean_ctor_get(v___x_1668_, 3);
v_getLevel_1674_ = lean_ctor_get(v___x_1668_, 4);
v_congrInfo_1675_ = lean_ctor_get(v___x_1668_, 5);
v_defEqI_1676_ = lean_ctor_get(v___x_1668_, 6);
v_extensions_1677_ = lean_ctor_get(v___x_1668_, 7);
v_issues_1678_ = lean_ctor_get(v___x_1668_, 8);
v_instanceOverrides_1679_ = lean_ctor_get(v___x_1668_, 10);
v_debug_1680_ = lean_ctor_get_uint8(v___x_1668_, sizeof(void*)*11);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1682_ = v___x_1668_;
v_isShared_1683_ = v_isSharedCheck_1701_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_instanceOverrides_1679_);
lean_inc(v_canon_1669_);
lean_inc(v_issues_1678_);
lean_inc(v_extensions_1677_);
lean_inc(v_defEqI_1676_);
lean_inc(v_congrInfo_1675_);
lean_inc(v_getLevel_1674_);
lean_inc(v_inferType_1673_);
lean_inc(v_proofInstInfo_1672_);
lean_inc(v_maxFVar_1671_);
lean_inc(v_share_1670_);
lean_dec(v___x_1668_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1701_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_cache_1684_; lean_object* v_cacheInType_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1700_; 
v_cache_1684_ = lean_ctor_get(v_canon_1669_, 0);
v_cacheInType_1685_ = lean_ctor_get(v_canon_1669_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_canon_1669_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1687_ = v_canon_1669_;
v_isShared_1688_ = v_isSharedCheck_1700_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_cacheInType_1685_);
lean_inc(v_cache_1684_);
lean_dec(v_canon_1669_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1700_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_inc(v_a_1664_);
v___x_1689_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1685_, v_e_1589_, v_a_1664_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_cache_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 9, v___x_1691_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_share_1670_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_maxFVar_1671_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_proofInstInfo_1672_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_inferType_1673_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_getLevel_1674_);
lean_ctor_set(v_reuseFailAlloc_1698_, 5, v_congrInfo_1675_);
lean_ctor_set(v_reuseFailAlloc_1698_, 6, v_defEqI_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 7, v_extensions_1677_);
lean_ctor_set(v_reuseFailAlloc_1698_, 8, v_issues_1678_);
lean_ctor_set(v_reuseFailAlloc_1698_, 9, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1698_, 10, v_instanceOverrides_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1698_, sizeof(void*)*11, v_debug_1680_);
v___x_1693_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_st_ref_set(v_a_1593_, v___x_1693_);
if (v_isShared_1667_ == 0)
{
v___x_1696_ = v___x_1666_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1664_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1589_);
return v___x_1663_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1719_ = l_Lean_mkConst(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1720_, lean_object* v_prop_1721_, lean_object* v_inst_1722_, lean_object* v_e_1723_, uint8_t v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; 
lean_inc_ref(v_prop_1721_);
v___x_1732_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1721_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1772_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1772_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1772_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___y_1738_; uint8_t v___y_1739_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1733_);
v___x_1748_ = l_Lean_Expr_app___override(v___x_1747_, v_a_1733_);
if (v_a_1724_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1748_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___y_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
if (lean_obj_tag(v_a_1750_) == 0)
{
lean_inc_ref(v_inst_1722_);
v___y_1752_ = v_inst_1722_;
goto v___jp_1751_;
}
else
{
lean_object* v_val_1761_; 
v_val_1761_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v_a_1750_, 1);
v___y_1752_ = v_val_1761_;
goto v___jp_1751_;
}
v___jp_1751_:
{
lean_object* v___x_1753_; 
lean_inc_ref(v_inst_1722_);
v___x_1753_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1722_, v___y_1752_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; size_t v___x_1755_; size_t v___x_1756_; uint8_t v___x_1757_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = lean_ptr_addr(v_prop_1721_);
lean_dec_ref(v_prop_1721_);
v___x_1756_ = lean_ptr_addr(v_a_1733_);
v___x_1757_ = lean_usize_dec_eq(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_inst_1722_);
v___y_1738_ = v_a_1754_;
v___y_1739_ = v___x_1757_;
goto v___jp_1737_;
}
else
{
size_t v___x_1758_; size_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = lean_ptr_addr(v_inst_1722_);
lean_dec_ref(v_inst_1722_);
v___x_1759_ = lean_ptr_addr(v_a_1754_);
v___x_1760_ = lean_usize_dec_eq(v___x_1758_, v___x_1759_);
v___y_1738_ = v_a_1754_;
v___y_1739_ = v___x_1760_;
goto v___jp_1737_;
}
}
else
{
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
v_a_1762_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1749_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1749_);
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
uint8_t v___x_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
v___x_1770_ = 0;
v___x_1771_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1722_, v___x_1748_, v___x_1770_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1771_;
}
v___jp_1737_:
{
if (v___y_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
lean_dec_ref(v_e_1723_);
v___x_1740_ = l_Lean_mkAppB(v_g_1720_, v_a_1733_, v___y_1738_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1740_);
v___x_1742_ = v___x_1735_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
else
{
lean_object* v___x_1745_; 
lean_dec_ref(v___y_1738_);
lean_dec(v_a_1733_);
lean_dec_ref(v_g_1720_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v_e_1723_);
v___x_1745_ = v___x_1735_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_e_1723_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1773_, lean_object* v_prop_1774_, lean_object* v_h_1775_, lean_object* v_e_1776_, uint8_t v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
if (v_a_1777_ == 0)
{
lean_object* v___x_1785_; lean_object* v_canon_1786_; lean_object* v_cache_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_st_ref_get(v_a_1779_);
v_canon_1786_ = lean_ctor_get(v___x_1785_, 9);
lean_inc_ref(v_canon_1786_);
lean_dec(v___x_1785_);
v_cache_1787_ = lean_ctor_get(v_canon_1786_, 0);
lean_inc_ref(v_cache_1787_);
lean_dec_ref(v_canon_1786_);
v___x_1788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1787_, v_e_1776_);
lean_dec_ref(v_cache_1787_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_e_1776_);
lean_dec_ref(v_h_1775_);
lean_dec_ref(v_prop_1774_);
lean_dec_ref(v_g_1773_);
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 0);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_val_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1797_; 
lean_dec(v___x_1788_);
lean_inc_ref(v_e_1776_);
v___x_1797_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1773_, v_prop_1774_, v_h_1775_, v_e_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1836_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1836_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1836_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v_canon_1803_; lean_object* v_share_1804_; lean_object* v_maxFVar_1805_; lean_object* v_proofInstInfo_1806_; lean_object* v_inferType_1807_; lean_object* v_getLevel_1808_; lean_object* v_congrInfo_1809_; lean_object* v_defEqI_1810_; lean_object* v_extensions_1811_; lean_object* v_issues_1812_; lean_object* v_instanceOverrides_1813_; uint8_t v_debug_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1835_; 
v___x_1802_ = lean_st_ref_take(v_a_1779_);
v_canon_1803_ = lean_ctor_get(v___x_1802_, 9);
v_share_1804_ = lean_ctor_get(v___x_1802_, 0);
v_maxFVar_1805_ = lean_ctor_get(v___x_1802_, 1);
v_proofInstInfo_1806_ = lean_ctor_get(v___x_1802_, 2);
v_inferType_1807_ = lean_ctor_get(v___x_1802_, 3);
v_getLevel_1808_ = lean_ctor_get(v___x_1802_, 4);
v_congrInfo_1809_ = lean_ctor_get(v___x_1802_, 5);
v_defEqI_1810_ = lean_ctor_get(v___x_1802_, 6);
v_extensions_1811_ = lean_ctor_get(v___x_1802_, 7);
v_issues_1812_ = lean_ctor_get(v___x_1802_, 8);
v_instanceOverrides_1813_ = lean_ctor_get(v___x_1802_, 10);
v_debug_1814_ = lean_ctor_get_uint8(v___x_1802_, sizeof(void*)*11);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1816_ = v___x_1802_;
v_isShared_1817_ = v_isSharedCheck_1835_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_instanceOverrides_1813_);
lean_inc(v_canon_1803_);
lean_inc(v_issues_1812_);
lean_inc(v_extensions_1811_);
lean_inc(v_defEqI_1810_);
lean_inc(v_congrInfo_1809_);
lean_inc(v_getLevel_1808_);
lean_inc(v_inferType_1807_);
lean_inc(v_proofInstInfo_1806_);
lean_inc(v_maxFVar_1805_);
lean_inc(v_share_1804_);
lean_dec(v___x_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1835_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_cache_1818_; lean_object* v_cacheInType_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1834_; 
v_cache_1818_ = lean_ctor_get(v_canon_1803_, 0);
v_cacheInType_1819_ = lean_ctor_get(v_canon_1803_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_canon_1803_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1821_ = v_canon_1803_;
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_cacheInType_1819_);
lean_inc(v_cache_1818_);
lean_dec(v_canon_1803_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_inc(v_a_1798_);
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1818_, v_e_1776_, v_a_1798_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_cacheInType_1819_);
v___x_1825_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 9, v___x_1825_);
v___x_1827_ = v___x_1816_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_share_1804_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_maxFVar_1805_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_proofInstInfo_1806_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_inferType_1807_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_getLevel_1808_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_congrInfo_1809_);
lean_ctor_set(v_reuseFailAlloc_1832_, 6, v_defEqI_1810_);
lean_ctor_set(v_reuseFailAlloc_1832_, 7, v_extensions_1811_);
lean_ctor_set(v_reuseFailAlloc_1832_, 8, v_issues_1812_);
lean_ctor_set(v_reuseFailAlloc_1832_, 9, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 10, v_instanceOverrides_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*11, v_debug_1814_);
v___x_1827_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_st_ref_set(v_a_1779_, v___x_1827_);
if (v_isShared_1801_ == 0)
{
v___x_1830_ = v___x_1800_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1798_);
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
}
}
}
else
{
lean_dec_ref(v_e_1776_);
return v___x_1797_;
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v_canon_1838_; lean_object* v_cacheInType_1839_; lean_object* v___x_1840_; 
v___x_1837_ = lean_st_ref_get(v_a_1779_);
v_canon_1838_ = lean_ctor_get(v___x_1837_, 9);
lean_inc_ref(v_canon_1838_);
lean_dec(v___x_1837_);
v_cacheInType_1839_ = lean_ctor_get(v_canon_1838_, 1);
lean_inc_ref(v_cacheInType_1839_);
lean_dec_ref(v_canon_1838_);
v___x_1840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1839_, v_e_1776_);
lean_dec_ref(v_cacheInType_1839_);
if (lean_obj_tag(v___x_1840_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v_e_1776_);
lean_dec_ref(v_h_1775_);
lean_dec_ref(v_prop_1774_);
lean_dec_ref(v_g_1773_);
v_val_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_val_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 0);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_val_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v___x_1840_);
lean_inc_ref(v_e_1776_);
v___x_1849_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1773_, v_prop_1774_, v_h_1775_, v_e_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1888_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1888_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1888_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v_canon_1855_; lean_object* v_share_1856_; lean_object* v_maxFVar_1857_; lean_object* v_proofInstInfo_1858_; lean_object* v_inferType_1859_; lean_object* v_getLevel_1860_; lean_object* v_congrInfo_1861_; lean_object* v_defEqI_1862_; lean_object* v_extensions_1863_; lean_object* v_issues_1864_; lean_object* v_instanceOverrides_1865_; uint8_t v_debug_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1887_; 
v___x_1854_ = lean_st_ref_take(v_a_1779_);
v_canon_1855_ = lean_ctor_get(v___x_1854_, 9);
v_share_1856_ = lean_ctor_get(v___x_1854_, 0);
v_maxFVar_1857_ = lean_ctor_get(v___x_1854_, 1);
v_proofInstInfo_1858_ = lean_ctor_get(v___x_1854_, 2);
v_inferType_1859_ = lean_ctor_get(v___x_1854_, 3);
v_getLevel_1860_ = lean_ctor_get(v___x_1854_, 4);
v_congrInfo_1861_ = lean_ctor_get(v___x_1854_, 5);
v_defEqI_1862_ = lean_ctor_get(v___x_1854_, 6);
v_extensions_1863_ = lean_ctor_get(v___x_1854_, 7);
v_issues_1864_ = lean_ctor_get(v___x_1854_, 8);
v_instanceOverrides_1865_ = lean_ctor_get(v___x_1854_, 10);
v_debug_1866_ = lean_ctor_get_uint8(v___x_1854_, sizeof(void*)*11);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1868_ = v___x_1854_;
v_isShared_1869_ = v_isSharedCheck_1887_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_instanceOverrides_1865_);
lean_inc(v_canon_1855_);
lean_inc(v_issues_1864_);
lean_inc(v_extensions_1863_);
lean_inc(v_defEqI_1862_);
lean_inc(v_congrInfo_1861_);
lean_inc(v_getLevel_1860_);
lean_inc(v_inferType_1859_);
lean_inc(v_proofInstInfo_1858_);
lean_inc(v_maxFVar_1857_);
lean_inc(v_share_1856_);
lean_dec(v___x_1854_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1887_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_cache_1870_; lean_object* v_cacheInType_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1886_; 
v_cache_1870_ = lean_ctor_get(v_canon_1855_, 0);
v_cacheInType_1871_ = lean_ctor_get(v_canon_1855_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_canon_1855_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1873_ = v_canon_1855_;
v_isShared_1874_ = v_isSharedCheck_1886_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_cacheInType_1871_);
lean_inc(v_cache_1870_);
lean_dec(v_canon_1855_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1886_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_inc(v_a_1850_);
v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1871_, v_e_1776_, v_a_1850_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1875_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 9, v___x_1877_);
v___x_1879_ = v___x_1868_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_share_1856_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_maxFVar_1857_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_proofInstInfo_1858_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_inferType_1859_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_getLevel_1860_);
lean_ctor_set(v_reuseFailAlloc_1884_, 5, v_congrInfo_1861_);
lean_ctor_set(v_reuseFailAlloc_1884_, 6, v_defEqI_1862_);
lean_ctor_set(v_reuseFailAlloc_1884_, 7, v_extensions_1863_);
lean_ctor_set(v_reuseFailAlloc_1884_, 8, v_issues_1864_);
lean_ctor_set(v_reuseFailAlloc_1884_, 9, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1884_, 10, v_instanceOverrides_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*11, v_debug_1866_);
v___x_1879_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_st_ref_set(v_a_1779_, v___x_1879_);
if (v_isShared_1853_ == 0)
{
v___x_1882_ = v___x_1852_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1850_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1776_);
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1889_, lean_object* v_prop_1890_, lean_object* v_h_1891_, lean_object* v_e_1892_, uint8_t v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_a_1902_; lean_object* v___y_1936_; 
if (v_a_1893_ == 0)
{
lean_object* v___x_1976_; lean_object* v_canon_1977_; lean_object* v_cache_1978_; lean_object* v___x_1979_; 
v___x_1976_ = lean_st_ref_get(v_a_1895_);
v_canon_1977_ = lean_ctor_get(v___x_1976_, 9);
lean_inc_ref(v_canon_1977_);
lean_dec(v___x_1976_);
v_cache_1978_ = lean_ctor_get(v_canon_1977_, 0);
lean_inc_ref(v_cache_1978_);
lean_dec_ref(v_canon_1977_);
v___x_1979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1978_, v_e_1892_);
lean_dec_ref(v_cache_1978_);
if (lean_obj_tag(v___x_1979_) == 1)
{
lean_object* v_val_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_e_1892_);
lean_dec_ref(v_h_1891_);
lean_dec_ref(v_prop_1890_);
lean_dec_ref(v_g_1889_);
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_val_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 0);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_val_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v___x_1988_; 
lean_dec(v___x_1979_);
lean_inc_ref(v_prop_1890_);
v___x_1988_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1890_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_n(v_a_1989_, 2);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_1989_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___y_1993_; uint8_t v___y_1994_; lean_object* v___y_1997_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
if (lean_obj_tag(v_a_1991_) == 0)
{
lean_inc_ref(v_h_1891_);
v___y_1997_ = v_h_1891_;
goto v___jp_1996_;
}
else
{
lean_object* v_val_2004_; 
v_val_2004_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v_a_1991_, 1);
v___y_1997_ = v_val_2004_;
goto v___jp_1996_;
}
v___jp_1992_:
{
if (v___y_1994_ == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_mkAppB(v_g_1889_, v_a_1989_, v___y_1993_);
v_a_1902_ = v___x_1995_;
goto v___jp_1901_;
}
else
{
lean_dec_ref(v___y_1993_);
lean_dec(v_a_1989_);
lean_dec_ref(v_g_1889_);
lean_inc_ref(v_e_1892_);
v_a_1902_ = v_e_1892_;
goto v___jp_1901_;
}
}
v___jp_1996_:
{
size_t v___x_1998_; size_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1998_ = lean_ptr_addr(v_prop_1890_);
lean_dec_ref(v_prop_1890_);
v___x_1999_ = lean_ptr_addr(v_a_1989_);
v___x_2000_ = lean_usize_dec_eq(v___x_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v_h_1891_);
v___y_1993_ = v___y_1997_;
v___y_1994_ = v___x_2000_;
goto v___jp_1992_;
}
else
{
size_t v___x_2001_; size_t v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_ptr_addr(v_h_1891_);
lean_dec_ref(v_h_1891_);
v___x_2002_ = lean_ptr_addr(v___y_1997_);
v___x_2003_ = lean_usize_dec_eq(v___x_2001_, v___x_2002_);
v___y_1993_ = v___y_1997_;
v___y_1994_ = v___x_2003_;
goto v___jp_1992_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1989_);
lean_dec_ref(v_e_1892_);
lean_dec_ref(v_h_1891_);
lean_dec_ref(v_prop_1890_);
lean_dec_ref(v_g_1889_);
v_a_2005_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1990_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1990_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_dec_ref(v_h_1891_);
lean_dec_ref(v_prop_1890_);
lean_dec_ref(v_g_1889_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_2013_; 
v_a_2013_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_1988_, 1);
v_a_1902_ = v_a_2013_;
goto v___jp_1901_;
}
else
{
lean_dec_ref(v_e_1892_);
return v___x_1988_;
}
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v_canon_2015_; lean_object* v_cacheInType_2016_; lean_object* v___x_2017_; 
lean_dec_ref(v_g_1889_);
v___x_2014_ = lean_st_ref_get(v_a_1895_);
v_canon_2015_ = lean_ctor_get(v___x_2014_, 9);
lean_inc_ref(v_canon_2015_);
lean_dec(v___x_2014_);
v_cacheInType_2016_ = lean_ctor_get(v_canon_2015_, 1);
lean_inc_ref(v_cacheInType_2016_);
lean_dec_ref(v_canon_2015_);
v___x_2017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2016_, v_e_1892_);
lean_dec_ref(v_cacheInType_2016_);
if (lean_obj_tag(v___x_2017_) == 1)
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_e_1892_);
lean_dec_ref(v_h_1891_);
lean_dec_ref(v_prop_1890_);
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v___x_2026_; 
lean_dec(v___x_2017_);
v___x_2026_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1890_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = 0;
v___x_2029_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1891_, v_a_2027_, v___x_2028_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
v___y_1936_ = v___x_2029_;
goto v___jp_1935_;
}
else
{
lean_dec_ref(v_h_1891_);
v___y_1936_ = v___x_2026_;
goto v___jp_1935_;
}
}
}
v___jp_1901_:
{
lean_object* v___x_1903_; lean_object* v_canon_1904_; lean_object* v_share_1905_; lean_object* v_maxFVar_1906_; lean_object* v_proofInstInfo_1907_; lean_object* v_inferType_1908_; lean_object* v_getLevel_1909_; lean_object* v_congrInfo_1910_; lean_object* v_defEqI_1911_; lean_object* v_extensions_1912_; lean_object* v_issues_1913_; lean_object* v_instanceOverrides_1914_; uint8_t v_debug_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1934_; 
v___x_1903_ = lean_st_ref_take(v_a_1895_);
v_canon_1904_ = lean_ctor_get(v___x_1903_, 9);
v_share_1905_ = lean_ctor_get(v___x_1903_, 0);
v_maxFVar_1906_ = lean_ctor_get(v___x_1903_, 1);
v_proofInstInfo_1907_ = lean_ctor_get(v___x_1903_, 2);
v_inferType_1908_ = lean_ctor_get(v___x_1903_, 3);
v_getLevel_1909_ = lean_ctor_get(v___x_1903_, 4);
v_congrInfo_1910_ = lean_ctor_get(v___x_1903_, 5);
v_defEqI_1911_ = lean_ctor_get(v___x_1903_, 6);
v_extensions_1912_ = lean_ctor_get(v___x_1903_, 7);
v_issues_1913_ = lean_ctor_get(v___x_1903_, 8);
v_instanceOverrides_1914_ = lean_ctor_get(v___x_1903_, 10);
v_debug_1915_ = lean_ctor_get_uint8(v___x_1903_, sizeof(void*)*11);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1917_ = v___x_1903_;
v_isShared_1918_ = v_isSharedCheck_1934_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_instanceOverrides_1914_);
lean_inc(v_canon_1904_);
lean_inc(v_issues_1913_);
lean_inc(v_extensions_1912_);
lean_inc(v_defEqI_1911_);
lean_inc(v_congrInfo_1910_);
lean_inc(v_getLevel_1909_);
lean_inc(v_inferType_1908_);
lean_inc(v_proofInstInfo_1907_);
lean_inc(v_maxFVar_1906_);
lean_inc(v_share_1905_);
lean_dec(v___x_1903_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1934_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_cache_1919_; lean_object* v_cacheInType_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1933_; 
v_cache_1919_ = lean_ctor_get(v_canon_1904_, 0);
v_cacheInType_1920_ = lean_ctor_get(v_canon_1904_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_canon_1904_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1922_ = v_canon_1904_;
v_isShared_1923_ = v_isSharedCheck_1933_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_cacheInType_1920_);
lean_inc(v_cache_1919_);
lean_dec(v_canon_1904_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1933_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_inc_ref(v_a_1902_);
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1919_, v_e_1892_, v_a_1902_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_cacheInType_1920_);
v___x_1926_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 9, v___x_1926_);
v___x_1928_ = v___x_1917_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_share_1905_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_maxFVar_1906_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_proofInstInfo_1907_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_inferType_1908_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_getLevel_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v_congrInfo_1910_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_defEqI_1911_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_extensions_1912_);
lean_ctor_set(v_reuseFailAlloc_1931_, 8, v_issues_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 9, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1931_, 10, v_instanceOverrides_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1931_, sizeof(void*)*11, v_debug_1915_);
v___x_1928_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_st_ref_set(v_a_1895_, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1902_);
return v___x_1930_;
}
}
}
}
}
v___jp_1935_:
{
if (lean_obj_tag(v___y_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1975_; 
v_a_1937_ = lean_ctor_get(v___y_1936_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1939_ = v___y_1936_;
v_isShared_1940_ = v_isSharedCheck_1975_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___y_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1975_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v_canon_1942_; lean_object* v_share_1943_; lean_object* v_maxFVar_1944_; lean_object* v_proofInstInfo_1945_; lean_object* v_inferType_1946_; lean_object* v_getLevel_1947_; lean_object* v_congrInfo_1948_; lean_object* v_defEqI_1949_; lean_object* v_extensions_1950_; lean_object* v_issues_1951_; lean_object* v_instanceOverrides_1952_; uint8_t v_debug_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1974_; 
v___x_1941_ = lean_st_ref_take(v_a_1895_);
v_canon_1942_ = lean_ctor_get(v___x_1941_, 9);
v_share_1943_ = lean_ctor_get(v___x_1941_, 0);
v_maxFVar_1944_ = lean_ctor_get(v___x_1941_, 1);
v_proofInstInfo_1945_ = lean_ctor_get(v___x_1941_, 2);
v_inferType_1946_ = lean_ctor_get(v___x_1941_, 3);
v_getLevel_1947_ = lean_ctor_get(v___x_1941_, 4);
v_congrInfo_1948_ = lean_ctor_get(v___x_1941_, 5);
v_defEqI_1949_ = lean_ctor_get(v___x_1941_, 6);
v_extensions_1950_ = lean_ctor_get(v___x_1941_, 7);
v_issues_1951_ = lean_ctor_get(v___x_1941_, 8);
v_instanceOverrides_1952_ = lean_ctor_get(v___x_1941_, 10);
v_debug_1953_ = lean_ctor_get_uint8(v___x_1941_, sizeof(void*)*11);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1955_ = v___x_1941_;
v_isShared_1956_ = v_isSharedCheck_1974_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_instanceOverrides_1952_);
lean_inc(v_canon_1942_);
lean_inc(v_issues_1951_);
lean_inc(v_extensions_1950_);
lean_inc(v_defEqI_1949_);
lean_inc(v_congrInfo_1948_);
lean_inc(v_getLevel_1947_);
lean_inc(v_inferType_1946_);
lean_inc(v_proofInstInfo_1945_);
lean_inc(v_maxFVar_1944_);
lean_inc(v_share_1943_);
lean_dec(v___x_1941_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1974_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v_cache_1957_; lean_object* v_cacheInType_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1973_; 
v_cache_1957_ = lean_ctor_get(v_canon_1942_, 0);
v_cacheInType_1958_ = lean_ctor_get(v_canon_1942_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_canon_1942_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1960_ = v_canon_1942_;
v_isShared_1961_ = v_isSharedCheck_1973_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_cacheInType_1958_);
lean_inc(v_cache_1957_);
lean_dec(v_canon_1942_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1973_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_inc(v_a_1937_);
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1958_, v_e_1892_, v_a_1937_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v___x_1962_);
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_cache_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 9, v___x_1964_);
v___x_1966_ = v___x_1955_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_share_1943_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_maxFVar_1944_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_proofInstInfo_1945_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_inferType_1946_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_getLevel_1947_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_congrInfo_1948_);
lean_ctor_set(v_reuseFailAlloc_1971_, 6, v_defEqI_1949_);
lean_ctor_set(v_reuseFailAlloc_1971_, 7, v_extensions_1950_);
lean_ctor_set(v_reuseFailAlloc_1971_, 8, v_issues_1951_);
lean_ctor_set(v_reuseFailAlloc_1971_, 9, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 10, v_instanceOverrides_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*11, v_debug_1953_);
v___x_1966_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_st_ref_set(v_a_1895_, v___x_1966_);
if (v_isShared_1940_ == 0)
{
v___x_1969_ = v___x_1939_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1937_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1892_);
return v___y_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2030_, lean_object* v_a_2031_, lean_object* v___x_2032_, lean_object* v_snd_2033_, uint8_t v___x_2034_, lean_object* v_fst_2035_, lean_object* v_____r_2036_, uint8_t v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_arg_x27_2046_; lean_object* v___x_2058_; 
lean_inc_ref(v___x_2032_);
v___x_2058_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2030_, v_a_2031_, v___x_2032_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; uint8_t v___x_2060_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_unbox(v_a_2059_);
lean_dec(v_a_2059_);
switch(v___x_2060_)
{
case 0:
{
lean_object* v___x_2061_; 
lean_inc_ref(v___x_2032_);
v___x_2061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2032_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v_arg_x27_2046_ = v_a_2062_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2063_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2061_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
case 1:
{
lean_object* v___x_2071_; 
lean_inc_ref(v___x_2032_);
v___x_2071_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2032_, v___y_2041_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; uint8_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2091_ = l_Lean_Expr_cleanupAnnotations(v_a_2072_);
v___x_2092_ = l_Lean_Expr_isApp(v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v___x_2091_);
v___y_2074_ = v___y_2037_;
v___y_2075_ = v___y_2038_;
v___y_2076_ = v___y_2039_;
v___y_2077_ = v___y_2040_;
v___y_2078_ = v___y_2041_;
v___y_2079_ = v___y_2042_;
v___y_2080_ = v___y_2043_;
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_arg_2093_ = lean_ctor_get(v___x_2091_, 1);
lean_inc_ref(v_arg_2093_);
v___x_2094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2091_);
v___x_2095_ = l_Lean_Expr_isApp(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec_ref(v___x_2094_);
lean_dec_ref(v_arg_2093_);
v___y_2074_ = v___y_2037_;
v___y_2075_ = v___y_2038_;
v___y_2076_ = v___y_2039_;
v___y_2077_ = v___y_2040_;
v___y_2078_ = v___y_2041_;
v___y_2079_ = v___y_2042_;
v___y_2080_ = v___y_2043_;
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_arg_2096_ = lean_ctor_get(v___x_2094_, 1);
lean_inc_ref(v_arg_2096_);
v___x_2097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2094_);
v___x_2098_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2099_ = l_Lean_Expr_isConstOf(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2101_ = l_Lean_Expr_isConstOf(v___x_2097_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec_ref(v___x_2097_);
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
v___y_2074_ = v___y_2037_;
v___y_2075_ = v___y_2038_;
v___y_2076_ = v___y_2039_;
v___y_2077_ = v___y_2040_;
v___y_2078_ = v___y_2041_;
v___y_2079_ = v___y_2042_;
v___y_2080_ = v___y_2043_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2102_; 
lean_inc_ref(v___x_2032_);
v___x_2102_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2097_, v_arg_2096_, v_arg_2093_, v___x_2032_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v_arg_x27_2046_ = v_a_2103_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2104_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2102_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; 
lean_inc_ref(v___x_2032_);
v___x_2112_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2097_, v_arg_2096_, v_arg_2093_, v___x_2032_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v_arg_x27_2046_ = v_a_2113_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2114_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2112_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2112_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
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
v___jp_2073_:
{
lean_object* v___x_2081_; 
lean_inc_ref(v___x_2032_);
v___x_2081_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2032_, v___x_2034_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v_arg_x27_2046_ = v_a_2082_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2083_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2081_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2081_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2122_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2071_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2071_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
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
default: 
{
lean_object* v___x_2130_; 
lean_inc_ref(v___x_2032_);
v___x_2130_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2032_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_arg_x27_2046_ = v_a_2131_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2132_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2130_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_fst_2035_);
lean_dec(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v_a_2140_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2058_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2058_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = lean_ptr_addr(v___x_2032_);
lean_dec_ref(v___x_2032_);
v___x_2048_ = lean_ptr_addr(v_arg_x27_2046_);
v___x_2049_ = lean_usize_dec_eq(v___x_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v_fst_2035_);
v___x_2050_ = lean_array_fset(v_snd_2033_, v_a_2031_, v_arg_x27_2046_);
v___x_2051_ = lean_box(v___x_2034_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2050_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_arg_x27_2046_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_fst_2035_);
lean_ctor_set(v___x_2055_, 1, v_snd_2033_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2152_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2153_ = l_Lean_Name_append(v___x_2152_, v___x_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2156_ = l_Lean_stringToMessageData(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2163_, lean_object* v___x_2164_, lean_object* v_a_2165_, lean_object* v_b_2166_, uint8_t v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___y_2176_; uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_lt(v_a_2165_, v_upperBound_2163_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v_a_2165_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_b_2166_);
return v___x_2199_;
}
else
{
lean_object* v_options_2200_; lean_object* v_fst_2201_; lean_object* v_snd_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2266_; 
v_options_2200_ = lean_ctor_get(v___y_2172_, 2);
v_fst_2201_ = lean_ctor_get(v_b_2166_, 0);
v_snd_2202_ = lean_ctor_get(v_b_2166_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_b_2166_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2204_ = v_b_2166_;
v_isShared_2205_ = v_isSharedCheck_2266_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_snd_2202_);
lean_inc(v_fst_2201_);
lean_dec(v_b_2166_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2266_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_inheritedTraceOptions_2206_; uint8_t v_hasTrace_2207_; lean_object* v___x_2208_; 
v_inheritedTraceOptions_2206_ = lean_ctor_get(v___y_2172_, 13);
v_hasTrace_2207_ = lean_ctor_get_uint8(v_options_2200_, sizeof(void*)*1);
v___x_2208_ = lean_array_fget(v_snd_2202_, v_a_2165_);
if (v_hasTrace_2207_ == 0)
{
lean_del_object(v___x_2204_);
goto v___jp_2209_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2213_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2214_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2206_, v_options_2200_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_del_object(v___x_2204_);
goto v___jp_2209_;
}
else
{
lean_object* v___x_2215_; 
lean_inc(v___x_2208_);
v___x_2215_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2164_, v_a_2165_, v___x_2208_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2172_);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2170_);
lean_inc(v___x_2208_);
v___x_2217_ = lean_infer_type(v___x_2208_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; uint8_t v___x_2245_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2245_ = lean_unbox(v_a_2216_);
lean_dec(v_a_2216_);
switch(v___x_2245_)
{
case 0:
{
lean_object* v___x_2246_; 
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2221_ = v___x_2246_;
goto v___jp_2220_;
}
case 1:
{
lean_object* v___x_2247_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2221_ = v___x_2247_;
goto v___jp_2220_;
}
case 2:
{
lean_object* v___x_2248_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2221_ = v___x_2248_;
goto v___jp_2220_;
}
default: 
{
lean_object* v___x_2249_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2221_ = v___x_2249_;
goto v___jp_2220_;
}
}
v___jp_2220_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_inc(v___y_2221_);
v___x_2222_ = l_Lean_MessageData_ofFormat(v___y_2221_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 7);
lean_ctor_set(v___x_2204_, 1, v___x_2222_);
lean_ctor_set(v___x_2204_, 0, v___x_2219_);
v___x_2224_ = v___x_2204_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2225_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
lean_inc(v___x_2208_);
v___x_2227_ = l_Lean_MessageData_ofExpr(v___x_2208_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l_Lean_MessageData_ofExpr(v_a_2218_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2212_, v___x_2232_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2164_, v_a_2165_, v___x_2208_, v_snd_2202_, v___x_2198_, v_fst_2201_, v_a_2234_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
v___y_2176_ = v___x_2235_;
goto v___jp_2175_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v___x_2208_);
lean_dec(v_snd_2202_);
lean_dec(v_fst_2201_);
lean_dec(v_a_2165_);
v_a_2236_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2233_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2233_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_a_2216_);
lean_dec(v___x_2208_);
lean_del_object(v___x_2204_);
lean_dec(v_snd_2202_);
lean_dec(v_fst_2201_);
lean_dec(v_a_2165_);
v_a_2250_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2217_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2217_);
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
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v___x_2208_);
lean_del_object(v___x_2204_);
lean_dec(v_snd_2202_);
lean_dec(v_fst_2201_);
lean_dec(v_a_2165_);
v_a_2258_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2215_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2215_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
v___jp_2209_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2164_, v_a_2165_, v___x_2208_, v_snd_2202_, v___x_2198_, v_fst_2201_, v___x_2210_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
v___y_2176_ = v___x_2211_;
goto v___jp_2175_;
}
}
}
v___jp_2175_:
{
if (lean_obj_tag(v___y_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2189_; 
v_a_2177_ = lean_ctor_get(v___y_2176_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___y_2176_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2179_ = v___y_2176_;
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___y_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
if (lean_obj_tag(v_a_2177_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; 
lean_dec(v_a_2165_);
v_a_2181_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v_a_2177_, 1);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_a_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_del_object(v___x_2179_);
v_a_2185_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v_a_2177_, 1);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_add(v_a_2165_, v___x_2186_);
lean_dec(v_a_2165_);
v_a_2165_ = v___x_2187_;
v_b_2166_ = v_a_2185_;
goto _start;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2165_);
v_a_2190_ = lean_ctor_get(v___y_2176_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___y_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___y_2176_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___y_2176_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, uint8_t v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___y_2280_; uint8_t v_modified_2281_; lean_object* v_f_2282_; uint8_t v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v_args_2338_; uint8_t v_modified_2339_; uint8_t v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; 
if (lean_obj_tag(v_x_2268_) == 5)
{
lean_object* v_fn_2375_; lean_object* v_arg_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_fn_2375_ = lean_ctor_get(v_x_2268_, 0);
lean_inc_ref(v_fn_2375_);
v_arg_2376_ = lean_ctor_get(v_x_2268_, 1);
lean_inc_ref(v_arg_2376_);
lean_dec_ref_known(v_x_2268_, 2);
v___x_2377_ = lean_array_set(v_x_2269_, v_x_2270_, v_arg_2376_);
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_nat_sub(v_x_2270_, v___x_2378_);
lean_dec(v_x_2270_);
v_x_2268_ = v_fn_2375_;
v_x_2269_ = v___x_2377_;
v_x_2270_ = v___x_2379_;
goto _start;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
lean_dec(v_x_2270_);
v___x_2381_ = lean_array_get_size(v_x_2269_);
v___x_2382_ = lean_unsigned_to_nat(2u);
v___x_2383_ = lean_nat_dec_eq(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
v___y_2354_ = v___y_2271_;
v___y_2355_ = v___y_2272_;
v___y_2356_ = v___y_2273_;
v___y_2357_ = v___y_2274_;
v___y_2358_ = v___y_2275_;
v___y_2359_ = v___y_2276_;
v___y_2360_ = v___y_2277_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2385_ = l_Lean_Expr_isConstOf(v_x_2268_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2387_ = l_Lean_Expr_isConstOf(v_x_2268_, v___x_2386_);
if (v___x_2387_ == 0)
{
v___y_2354_ = v___y_2271_;
v___y_2355_ = v___y_2272_;
v___y_2356_ = v___y_2273_;
v___y_2357_ = v___y_2274_;
v___y_2358_ = v___y_2275_;
v___y_2359_ = v___y_2276_;
v___y_2360_ = v___y_2277_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2388_ = l_Lean_instInhabitedExpr;
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_array_get(v___x_2388_, v_x_2269_, v___x_2389_);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_array_get(v___x_2388_, v_x_2269_, v___x_2391_);
lean_dec_ref(v_x_2269_);
v___x_2393_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2268_, v___x_2390_, v___x_2392_, v_e_2267_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2393_;
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_prop_2396_; lean_object* v___x_2397_; 
v___x_2394_ = l_Lean_instInhabitedExpr;
v___x_2395_ = lean_unsigned_to_nat(0u);
v_prop_2396_ = lean_array_get_borrowed(v___x_2394_, v_x_2269_, v___x_2395_);
lean_inc(v_prop_2396_);
v___x_2397_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2396_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2414_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2414_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2414_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
size_t v___x_2402_; size_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_ptr_addr(v_prop_2396_);
v___x_2403_ = lean_ptr_addr(v_a_2398_);
v___x_2404_ = lean_usize_dec_eq(v___x_2402_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec_ref(v_e_2267_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_array_get(v___x_2394_, v_x_2269_, v___x_2405_);
lean_dec_ref(v_x_2269_);
v___x_2407_ = l_Lean_mkAppB(v_x_2268_, v_a_2398_, v___x_2406_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2407_);
v___x_2409_ = v___x_2400_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
else
{
lean_object* v___x_2412_; 
lean_dec(v_a_2398_);
lean_dec_ref(v_x_2269_);
lean_dec_ref(v_x_2268_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v_e_2267_);
v___x_2412_ = v___x_2400_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_e_2267_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_dec_ref(v_x_2269_);
lean_dec_ref(v_x_2268_);
lean_dec_ref(v_e_2267_);
return v___x_2397_;
}
}
}
}
v___jp_2279_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_box(0);
lean_inc_ref(v_f_2282_);
v___x_2291_ = l_Lean_Meta_getFunInfo(v_f_2282_, v___x_2290_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v_paramInfo_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2327_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v_paramInfo_2293_ = lean_ctor_get(v_a_2292_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_a_2292_, 1);
lean_dec(v_unused_2328_);
v___x_2295_ = v_a_2292_;
v_isShared_2296_ = v_isSharedCheck_2327_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_paramInfo_2293_);
lean_dec(v_a_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2327_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2297_ = lean_array_get_size(v___y_2280_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_box(v_modified_2281_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___y_2280_);
lean_ctor_set(v___x_2295_, 0, v___x_2299_);
v___x_2301_ = v___x_2295_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___y_2280_);
v___x_2301_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2297_, v_paramInfo_2293_, v___x_2298_, v___x_2301_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec_ref(v_paramInfo_2293_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2317_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_fst_2307_; uint8_t v___x_2308_; 
v_fst_2307_ = lean_ctor_get(v_a_2303_, 0);
v___x_2308_ = lean_unbox(v_fst_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_f_2282_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_e_2267_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_e_2267_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v_snd_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec_ref(v_e_2267_);
v_snd_2312_ = lean_ctor_get(v_a_2303_, 1);
lean_inc(v_snd_2312_);
lean_dec(v_a_2303_);
v___x_2313_ = l_Lean_mkAppN(v_f_2282_, v_snd_2312_);
lean_dec(v_snd_2312_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2313_);
v___x_2315_ = v___x_2305_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_f_2282_);
lean_dec_ref(v_e_2267_);
v_a_2318_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2302_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2302_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_f_2282_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_e_2267_);
v_a_2329_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2291_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2291_);
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
v___jp_2337_:
{
lean_object* v___x_2347_; 
lean_inc_ref(v_x_2268_);
v___x_2347_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2268_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; size_t v___x_2349_; size_t v___x_2350_; uint8_t v___x_2351_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_ptr_addr(v_x_2268_);
v___x_2350_ = lean_ptr_addr(v_a_2348_);
v___x_2351_ = lean_usize_dec_eq(v___x_2349_, v___x_2350_);
if (v___x_2351_ == 0)
{
uint8_t v___x_2352_; 
lean_dec_ref(v_x_2268_);
v___x_2352_ = 1;
v___y_2280_ = v_args_2338_;
v_modified_2281_ = v___x_2352_;
v_f_2282_ = v_a_2348_;
v___y_2283_ = v___y_2340_;
v___y_2284_ = v___y_2341_;
v___y_2285_ = v___y_2342_;
v___y_2286_ = v___y_2343_;
v___y_2287_ = v___y_2344_;
v___y_2288_ = v___y_2345_;
v___y_2289_ = v___y_2346_;
goto v___jp_2279_;
}
else
{
lean_dec(v_a_2348_);
v___y_2280_ = v_args_2338_;
v_modified_2281_ = v_modified_2339_;
v_f_2282_ = v_x_2268_;
v___y_2283_ = v___y_2340_;
v___y_2284_ = v___y_2341_;
v___y_2285_ = v___y_2342_;
v___y_2286_ = v___y_2343_;
v___y_2287_ = v___y_2344_;
v___y_2288_ = v___y_2345_;
v___y_2289_ = v___y_2346_;
goto v___jp_2279_;
}
}
else
{
lean_dec_ref(v_args_2338_);
lean_dec_ref(v_x_2268_);
lean_dec_ref(v_e_2267_);
return v___x_2347_;
}
}
v___jp_2353_:
{
uint8_t v_modified_2361_; lean_object* v___x_2362_; uint8_t v_modified_2363_; 
v_modified_2361_ = 0;
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2363_ = l_Lean_Expr_isConstOf(v_x_2268_, v___x_2362_);
if (v_modified_2363_ == 0)
{
v_args_2338_ = v_x_2269_;
v_modified_2339_ = v_modified_2361_;
v___y_2340_ = v___y_2354_;
v___y_2341_ = v___y_2355_;
v___y_2342_ = v___y_2356_;
v___y_2343_ = v___y_2357_;
v___y_2344_ = v___y_2358_;
v___y_2345_ = v___y_2359_;
v___y_2346_ = v___y_2360_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2364_; 
lean_inc_ref(v_x_2269_);
v___x_2364_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2269_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
if (lean_obj_tag(v_a_2365_) == 1)
{
lean_object* v_val_2366_; 
lean_dec_ref(v_x_2269_);
v_val_2366_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v_a_2365_, 1);
v_args_2338_ = v_val_2366_;
v_modified_2339_ = v_modified_2363_;
v___y_2340_ = v___y_2354_;
v___y_2341_ = v___y_2355_;
v___y_2342_ = v___y_2356_;
v___y_2343_ = v___y_2357_;
v___y_2344_ = v___y_2358_;
v___y_2345_ = v___y_2359_;
v___y_2346_ = v___y_2360_;
goto v___jp_2337_;
}
else
{
lean_dec(v_a_2365_);
v_args_2338_ = v_x_2269_;
v_modified_2339_ = v_modified_2361_;
v___y_2340_ = v___y_2354_;
v___y_2341_ = v___y_2355_;
v___y_2342_ = v___y_2356_;
v___y_2343_ = v___y_2357_;
v___y_2344_ = v___y_2358_;
v___y_2345_ = v___y_2359_;
v___y_2346_ = v___y_2360_;
goto v___jp_2337_;
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_x_2269_);
lean_dec_ref(v_x_2268_);
lean_dec_ref(v_e_2267_);
v_a_2367_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2364_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2364_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2415_, uint8_t v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_dummy_2424_; lean_object* v_nargs_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_dummy_2424_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2425_ = l_Lean_Expr_getAppNumArgs(v_e_2415_);
lean_inc(v_nargs_2425_);
v___x_2426_ = lean_mk_array(v_nargs_2425_, v_dummy_2424_);
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = lean_nat_sub(v_nargs_2425_, v___x_2427_);
lean_dec(v_nargs_2425_);
lean_inc_ref(v_e_2415_);
v___x_2429_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2415_, v_e_2415_, v___x_2426_, v___x_2428_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2430_, uint8_t v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2440_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2441_;
}
else
{
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2442_, uint8_t v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2442_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
if (lean_obj_tag(v_a_2452_) == 0)
{
lean_object* v_val_2453_; lean_object* v___x_2454_; 
lean_dec_ref(v_e_2442_);
v_val_2453_ = lean_ctor_get(v_a_2452_, 0);
lean_inc_ref(v_val_2453_);
lean_dec_ref_known(v_a_2452_, 1);
v___x_2454_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2453_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; 
lean_dec(v_a_2452_);
v___x_2455_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2456_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2467_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2467_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2467_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
if (lean_obj_tag(v_a_2458_) == 0)
{
lean_object* v_val_2462_; lean_object* v___x_2463_; 
lean_del_object(v___x_2460_);
lean_dec(v_a_2456_);
v_val_2462_ = lean_ctor_get(v_a_2458_, 0);
lean_inc_ref(v_val_2462_);
lean_dec_ref_known(v_a_2458_, 1);
v___x_2463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2462_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2463_;
}
else
{
lean_object* v___x_2465_; 
lean_dec(v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v_a_2456_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2456_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_a_2456_);
v_a_2468_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2457_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2457_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_e_2442_);
v_a_2476_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2451_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2451_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2490_, uint8_t v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
lean_inc_ref(v_e_2490_);
v___x_2499_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2490_, v_a_2495_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2511_ = l_Lean_Expr_cleanupAnnotations(v_a_2500_);
v___x_2512_ = l_Lean_Expr_isApp(v___x_2511_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2502_ = v_a_2491_;
v___y_2503_ = v_a_2492_;
v___y_2504_ = v_a_2493_;
v___y_2505_ = v_a_2494_;
v___y_2506_ = v_a_2495_;
v___y_2507_ = v_a_2496_;
v___y_2508_ = v_a_2497_;
goto v___jp_2501_;
}
else
{
lean_object* v_arg_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_arg_2513_ = lean_ctor_get(v___x_2511_, 1);
lean_inc_ref(v_arg_2513_);
v___x_2514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2511_);
v___x_2515_ = l_Lean_Expr_isApp(v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_arg_2513_);
v___y_2502_ = v_a_2491_;
v___y_2503_ = v_a_2492_;
v___y_2504_ = v_a_2493_;
v___y_2505_ = v_a_2494_;
v___y_2506_ = v_a_2495_;
v___y_2507_ = v_a_2496_;
v___y_2508_ = v_a_2497_;
goto v___jp_2501_;
}
else
{
lean_object* v_arg_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_arg_2516_ = lean_ctor_get(v___x_2514_, 1);
lean_inc_ref(v_arg_2516_);
v___x_2517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2514_);
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2519_ = l_Lean_Expr_isConstOf(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_dec_ref(v___x_2517_);
lean_dec_ref(v_arg_2516_);
lean_dec_ref(v_arg_2513_);
v___y_2502_ = v_a_2491_;
v___y_2503_ = v_a_2492_;
v___y_2504_ = v_a_2493_;
v___y_2505_ = v_a_2494_;
v___y_2506_ = v_a_2495_;
v___y_2507_ = v_a_2496_;
v___y_2508_ = v_a_2497_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2517_, v_arg_2516_, v_arg_2513_, v_e_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2520_;
}
}
}
v___jp_2501_:
{
uint8_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = 0;
v___x_2510_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2490_, v___x_2509_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2510_;
}
}
else
{
lean_dec_ref(v_e_2490_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2521_, lean_object* v_00_u03b1_2522_, lean_object* v_c_2523_, lean_object* v_inst_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_, uint8_t v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2523_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; uint8_t v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc_n(v_a_2536_, 2);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2536_);
if (v___x_2537_ == 0)
{
uint8_t v___x_2538_; 
lean_inc(v_a_2536_);
v___x_2538_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2536_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2522_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2541_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2524_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2525_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2554_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = l_Lean_mkApp5(v_f_2521_, v_a_2540_, v_a_2536_, v_a_2542_, v_a_2544_, v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_dec(v_a_2544_);
lean_dec(v_a_2542_);
lean_dec(v_a_2540_);
lean_dec(v_a_2536_);
lean_dec_ref(v_f_2521_);
return v___x_2545_;
}
}
else
{
lean_dec(v_a_2542_);
lean_dec(v_a_2540_);
lean_dec(v_a_2536_);
lean_dec_ref(v_b_2526_);
lean_dec_ref(v_f_2521_);
return v___x_2543_;
}
}
else
{
lean_dec(v_a_2540_);
lean_dec(v_a_2536_);
lean_dec_ref(v_b_2526_);
lean_dec_ref(v_a_2525_);
lean_dec_ref(v_f_2521_);
return v___x_2541_;
}
}
else
{
lean_dec(v_a_2536_);
lean_dec_ref(v_b_2526_);
lean_dec_ref(v_a_2525_);
lean_dec_ref(v_inst_2524_);
lean_dec_ref(v_f_2521_);
return v___x_2539_;
}
}
else
{
lean_object* v___x_2555_; 
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2525_);
lean_dec_ref(v_inst_2524_);
lean_dec_ref(v_00_u03b1_2522_);
lean_dec_ref(v_f_2521_);
v___x_2555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2555_;
}
}
else
{
lean_object* v___x_2556_; 
lean_dec(v_a_2536_);
lean_dec_ref(v_b_2526_);
lean_dec_ref(v_inst_2524_);
lean_dec_ref(v_00_u03b1_2522_);
lean_dec_ref(v_f_2521_);
v___x_2556_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2525_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2556_;
}
}
else
{
lean_dec_ref(v_b_2526_);
lean_dec_ref(v_a_2525_);
lean_dec_ref(v_inst_2524_);
lean_dec_ref(v_00_u03b1_2522_);
lean_dec_ref(v_f_2521_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2557_, lean_object* v_00_u03b1_2558_, lean_object* v_c_2559_, lean_object* v_a_2560_, lean_object* v_b_2561_, uint8_t v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2559_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; uint8_t v___x_2572_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_n(v_a_2571_, 2);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = l_Lean_Expr_isBoolTrue(v_a_2571_);
if (v___x_2572_ == 0)
{
uint8_t v___x_2573_; 
lean_inc(v_a_2571_);
v___x_2573_ = l_Lean_Expr_isBoolFalse(v_a_2571_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
v___x_2574_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2558_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2560_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = l_Lean_mkApp4(v_f_2557_, v_a_2575_, v_a_2571_, v_a_2577_, v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2585_ = v___x_2581_;
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
else
{
lean_dec(v_a_2577_);
lean_dec(v_a_2575_);
lean_dec(v_a_2571_);
lean_dec_ref(v_f_2557_);
return v___x_2578_;
}
}
else
{
lean_dec(v_a_2575_);
lean_dec(v_a_2571_);
lean_dec_ref(v_b_2561_);
lean_dec_ref(v_f_2557_);
return v___x_2576_;
}
}
else
{
lean_dec(v_a_2571_);
lean_dec_ref(v_b_2561_);
lean_dec_ref(v_a_2560_);
lean_dec_ref(v_f_2557_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2588_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2560_);
lean_dec_ref(v_00_u03b1_2558_);
lean_dec_ref(v_f_2557_);
v___x_2588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2588_;
}
}
else
{
lean_object* v___x_2589_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_b_2561_);
lean_dec_ref(v_00_u03b1_2558_);
lean_dec_ref(v_f_2557_);
v___x_2589_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2560_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2589_;
}
}
else
{
lean_dec_ref(v_b_2561_);
lean_dec_ref(v_a_2560_);
lean_dec_ref(v_00_u03b1_2558_);
lean_dec_ref(v_f_2557_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2590_, uint8_t v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v___x_2599_; 
lean_inc_ref(v_e_2590_);
v___x_2599_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2590_, v_a_2595_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; uint8_t v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2625_ = l_Lean_Expr_cleanupAnnotations(v_a_2600_);
v___x_2626_ = l_Lean_Expr_isApp(v___x_2625_);
if (v___x_2626_ == 0)
{
lean_dec_ref(v___x_2625_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v_arg_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_arg_2627_ = lean_ctor_get(v___x_2625_, 1);
lean_inc_ref(v_arg_2627_);
v___x_2628_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2625_);
v___x_2629_ = l_Lean_Expr_isApp(v___x_2628_);
if (v___x_2629_ == 0)
{
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_arg_2627_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v_arg_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_arg_2630_ = lean_ctor_get(v___x_2628_, 1);
lean_inc_ref(v_arg_2630_);
v___x_2631_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2628_);
v___x_2632_ = l_Lean_Expr_isApp(v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec_ref(v___x_2631_);
lean_dec_ref(v_arg_2630_);
lean_dec_ref(v_arg_2627_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v_arg_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v_arg_2633_ = lean_ctor_get(v___x_2631_, 1);
lean_inc_ref(v_arg_2633_);
v___x_2634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2631_);
v___x_2635_ = l_Lean_Expr_isApp(v___x_2634_);
if (v___x_2635_ == 0)
{
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_arg_2630_);
lean_dec_ref(v_arg_2627_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v_arg_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v_arg_2636_ = lean_ctor_get(v___x_2634_, 1);
lean_inc_ref(v_arg_2636_);
v___x_2637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2634_);
v___x_2638_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2639_ = l_Lean_Expr_isConstOf(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_Expr_isApp(v___x_2637_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v___x_2637_);
lean_dec_ref(v_arg_2636_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_arg_2630_);
lean_dec_ref(v_arg_2627_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v_arg_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v_arg_2641_ = lean_ctor_get(v___x_2637_, 1);
lean_inc_ref(v_arg_2641_);
v___x_2642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2637_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2644_ = l_Lean_Expr_isConstOf(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_dec_ref(v___x_2642_);
lean_dec_ref(v_arg_2641_);
lean_dec_ref(v_arg_2636_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_arg_2630_);
lean_dec_ref(v_arg_2627_);
v___y_2602_ = v_a_2591_;
v___y_2603_ = v_a_2592_;
v___y_2604_ = v_a_2593_;
v___y_2605_ = v_a_2594_;
v___y_2606_ = v_a_2595_;
v___y_2607_ = v_a_2596_;
v___y_2608_ = v_a_2597_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2645_; 
lean_dec_ref(v_e_2590_);
v___x_2645_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2642_, v_arg_2641_, v_arg_2636_, v_arg_2633_, v_arg_2630_, v_arg_2627_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
return v___x_2645_;
}
}
}
else
{
lean_object* v___x_2646_; 
lean_dec_ref(v_e_2590_);
v___x_2646_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2637_, v_arg_2636_, v_arg_2633_, v_arg_2630_, v_arg_2627_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
return v___x_2646_;
}
}
}
}
}
v___jp_2601_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Expr_getAppFn(v_e_2590_);
if (lean_obj_tag(v___x_2609_) == 4)
{
lean_object* v_declName_2610_; lean_object* v___x_2611_; 
v_declName_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_declName_2610_);
lean_dec_ref_known(v___x_2609_, 2);
v___x_2611_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2610_, v___y_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; uint8_t v___x_2613_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2590_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2590_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2615_;
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_e_2590_);
v_a_2616_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2611_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2611_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref(v___x_2609_);
v___x_2624_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2590_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2624_;
}
}
}
else
{
lean_dec_ref(v_e_2590_);
return v___x_2599_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2651_ = lean_unsigned_to_nat(18u);
v___x_2652_ = lean_unsigned_to_nat(1896u);
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2655_ = l_mkPanicMessageWithDecl(v___x_2654_, v___x_2653_, v___x_2652_, v___x_2651_, v___x_2650_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2656_, uint8_t v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = l_Lean_Expr_projExpr_x21(v_e_2656_);
v___x_2666_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2665_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___y_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
if (lean_obj_tag(v_e_2656_) == 11)
{
lean_object* v_typeName_2691_; lean_object* v_idx_2692_; lean_object* v_struct_2693_; size_t v___x_2694_; size_t v___x_2695_; uint8_t v___x_2696_; 
v_typeName_2691_ = lean_ctor_get(v_e_2656_, 0);
v_idx_2692_ = lean_ctor_get(v_e_2656_, 1);
v_struct_2693_ = lean_ctor_get(v_e_2656_, 2);
v___x_2694_ = lean_ptr_addr(v_struct_2693_);
v___x_2695_ = lean_ptr_addr(v_a_2667_);
v___x_2696_ = lean_usize_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; 
lean_inc(v_idx_2692_);
lean_inc(v_typeName_2691_);
lean_dec_ref_known(v_e_2656_, 3);
v___x_2697_ = l_Lean_Expr_proj___override(v_typeName_2691_, v_idx_2692_, v_a_2667_);
v___y_2669_ = v___x_2697_;
goto v___jp_2668_;
}
else
{
lean_dec(v_a_2667_);
v___y_2669_ = v_e_2656_;
goto v___jp_2668_;
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec(v_a_2667_);
lean_dec_ref(v_e_2656_);
v___x_2698_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2699_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2698_);
v___y_2669_ = v___x_2699_;
goto v___jp_2668_;
}
v___jp_2668_:
{
lean_object* v___x_2670_; 
lean_inc_ref(v___y_2669_);
v___x_2670_ = l_Lean_Meta_reduceProj_x3f(v___y_2669_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2682_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
if (lean_obj_tag(v_a_2671_) == 0)
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___y_2669_);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___y_2669_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
lean_object* v_val_2678_; lean_object* v___x_2680_; 
lean_dec_ref(v___y_2669_);
v_val_2678_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_val_2678_);
lean_dec_ref_known(v_a_2671_, 1);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v_val_2678_);
v___x_2680_ = v___x_2673_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_val_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v___y_2669_);
v_a_2683_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2670_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2670_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2656_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2700_, uint8_t v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
switch(lean_obj_tag(v_e_2700_))
{
case 7:
{
lean_object* v___x_2709_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2701_ == 0)
{
lean_object* v___x_2710_; lean_object* v_canon_2711_; lean_object* v_cache_2712_; lean_object* v___x_2713_; 
v___x_2710_ = lean_st_ref_get(v_a_2703_);
v_canon_2711_ = lean_ctor_get(v___x_2710_, 9);
lean_inc_ref(v_canon_2711_);
lean_dec(v___x_2710_);
v_cache_2712_ = lean_ctor_get(v_canon_2711_, 0);
lean_inc_ref(v_cache_2712_);
lean_dec_ref(v_canon_2711_);
v___x_2713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2712_, v_e_2700_);
lean_dec_ref(v_cache_2712_);
if (lean_obj_tag(v___x_2713_) == 1)
{
lean_object* v_val_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_val_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 0);
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_val_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v___x_2722_; 
lean_dec(v___x_2713_);
lean_inc_ref(v_e_2700_);
v___x_2722_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2709_, v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2761_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2761_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2761_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v_canon_2728_; lean_object* v_share_2729_; lean_object* v_maxFVar_2730_; lean_object* v_proofInstInfo_2731_; lean_object* v_inferType_2732_; lean_object* v_getLevel_2733_; lean_object* v_congrInfo_2734_; lean_object* v_defEqI_2735_; lean_object* v_extensions_2736_; lean_object* v_issues_2737_; lean_object* v_instanceOverrides_2738_; uint8_t v_debug_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2760_; 
v___x_2727_ = lean_st_ref_take(v_a_2703_);
v_canon_2728_ = lean_ctor_get(v___x_2727_, 9);
v_share_2729_ = lean_ctor_get(v___x_2727_, 0);
v_maxFVar_2730_ = lean_ctor_get(v___x_2727_, 1);
v_proofInstInfo_2731_ = lean_ctor_get(v___x_2727_, 2);
v_inferType_2732_ = lean_ctor_get(v___x_2727_, 3);
v_getLevel_2733_ = lean_ctor_get(v___x_2727_, 4);
v_congrInfo_2734_ = lean_ctor_get(v___x_2727_, 5);
v_defEqI_2735_ = lean_ctor_get(v___x_2727_, 6);
v_extensions_2736_ = lean_ctor_get(v___x_2727_, 7);
v_issues_2737_ = lean_ctor_get(v___x_2727_, 8);
v_instanceOverrides_2738_ = lean_ctor_get(v___x_2727_, 10);
v_debug_2739_ = lean_ctor_get_uint8(v___x_2727_, sizeof(void*)*11);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2741_ = v___x_2727_;
v_isShared_2742_ = v_isSharedCheck_2760_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_instanceOverrides_2738_);
lean_inc(v_canon_2728_);
lean_inc(v_issues_2737_);
lean_inc(v_extensions_2736_);
lean_inc(v_defEqI_2735_);
lean_inc(v_congrInfo_2734_);
lean_inc(v_getLevel_2733_);
lean_inc(v_inferType_2732_);
lean_inc(v_proofInstInfo_2731_);
lean_inc(v_maxFVar_2730_);
lean_inc(v_share_2729_);
lean_dec(v___x_2727_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2760_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_cache_2743_; lean_object* v_cacheInType_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2759_; 
v_cache_2743_ = lean_ctor_get(v_canon_2728_, 0);
v_cacheInType_2744_ = lean_ctor_get(v_canon_2728_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_canon_2728_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2746_ = v_canon_2728_;
v_isShared_2747_ = v_isSharedCheck_2759_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_cacheInType_2744_);
lean_inc(v_cache_2743_);
lean_dec(v_canon_2728_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2759_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
lean_inc(v_a_2723_);
v___x_2748_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2743_, v_e_2700_, v_a_2723_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2748_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_cacheInType_2744_);
v___x_2750_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2752_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 9, v___x_2750_);
v___x_2752_ = v___x_2741_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_share_2729_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_maxFVar_2730_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_proofInstInfo_2731_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_inferType_2732_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_getLevel_2733_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v_congrInfo_2734_);
lean_ctor_set(v_reuseFailAlloc_2757_, 6, v_defEqI_2735_);
lean_ctor_set(v_reuseFailAlloc_2757_, 7, v_extensions_2736_);
lean_ctor_set(v_reuseFailAlloc_2757_, 8, v_issues_2737_);
lean_ctor_set(v_reuseFailAlloc_2757_, 9, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2757_, 10, v_instanceOverrides_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*11, v_debug_2739_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = lean_st_ref_set(v_a_2703_, v___x_2752_);
if (v_isShared_2726_ == 0)
{
v___x_2755_ = v___x_2725_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2723_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_2722_;
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v_canon_2763_; lean_object* v_cacheInType_2764_; lean_object* v___x_2765_; 
v___x_2762_ = lean_st_ref_get(v_a_2703_);
v_canon_2763_ = lean_ctor_get(v___x_2762_, 9);
lean_inc_ref(v_canon_2763_);
lean_dec(v___x_2762_);
v_cacheInType_2764_ = lean_ctor_get(v_canon_2763_, 1);
lean_inc_ref(v_cacheInType_2764_);
lean_dec_ref(v_canon_2763_);
v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2764_, v_e_2700_);
lean_dec_ref(v_cacheInType_2764_);
if (lean_obj_tag(v___x_2765_) == 1)
{
lean_object* v_val_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_val_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 0);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_val_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
else
{
lean_object* v___x_2774_; 
lean_dec(v___x_2765_);
lean_inc_ref(v_e_2700_);
v___x_2774_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2709_, v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2813_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2813_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2813_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v_canon_2780_; lean_object* v_share_2781_; lean_object* v_maxFVar_2782_; lean_object* v_proofInstInfo_2783_; lean_object* v_inferType_2784_; lean_object* v_getLevel_2785_; lean_object* v_congrInfo_2786_; lean_object* v_defEqI_2787_; lean_object* v_extensions_2788_; lean_object* v_issues_2789_; lean_object* v_instanceOverrides_2790_; uint8_t v_debug_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2812_; 
v___x_2779_ = lean_st_ref_take(v_a_2703_);
v_canon_2780_ = lean_ctor_get(v___x_2779_, 9);
v_share_2781_ = lean_ctor_get(v___x_2779_, 0);
v_maxFVar_2782_ = lean_ctor_get(v___x_2779_, 1);
v_proofInstInfo_2783_ = lean_ctor_get(v___x_2779_, 2);
v_inferType_2784_ = lean_ctor_get(v___x_2779_, 3);
v_getLevel_2785_ = lean_ctor_get(v___x_2779_, 4);
v_congrInfo_2786_ = lean_ctor_get(v___x_2779_, 5);
v_defEqI_2787_ = lean_ctor_get(v___x_2779_, 6);
v_extensions_2788_ = lean_ctor_get(v___x_2779_, 7);
v_issues_2789_ = lean_ctor_get(v___x_2779_, 8);
v_instanceOverrides_2790_ = lean_ctor_get(v___x_2779_, 10);
v_debug_2791_ = lean_ctor_get_uint8(v___x_2779_, sizeof(void*)*11);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2793_ = v___x_2779_;
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_instanceOverrides_2790_);
lean_inc(v_canon_2780_);
lean_inc(v_issues_2789_);
lean_inc(v_extensions_2788_);
lean_inc(v_defEqI_2787_);
lean_inc(v_congrInfo_2786_);
lean_inc(v_getLevel_2785_);
lean_inc(v_inferType_2784_);
lean_inc(v_proofInstInfo_2783_);
lean_inc(v_maxFVar_2782_);
lean_inc(v_share_2781_);
lean_dec(v___x_2779_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_cache_2795_; lean_object* v_cacheInType_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2811_; 
v_cache_2795_ = lean_ctor_get(v_canon_2780_, 0);
v_cacheInType_2796_ = lean_ctor_get(v_canon_2780_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_canon_2780_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2798_ = v_canon_2780_;
v_isShared_2799_ = v_isSharedCheck_2811_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_cacheInType_2796_);
lean_inc(v_cache_2795_);
lean_dec(v_canon_2780_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2811_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_inc(v_a_2775_);
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2796_, v_e_2700_, v_a_2775_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 1, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_cache_2795_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 9, v___x_2802_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_share_2781_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_maxFVar_2782_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_proofInstInfo_2783_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_inferType_2784_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_getLevel_2785_);
lean_ctor_set(v_reuseFailAlloc_2809_, 5, v_congrInfo_2786_);
lean_ctor_set(v_reuseFailAlloc_2809_, 6, v_defEqI_2787_);
lean_ctor_set(v_reuseFailAlloc_2809_, 7, v_extensions_2788_);
lean_ctor_set(v_reuseFailAlloc_2809_, 8, v_issues_2789_);
lean_ctor_set(v_reuseFailAlloc_2809_, 9, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2809_, 10, v_instanceOverrides_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*11, v_debug_2791_);
v___x_2804_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = lean_st_ref_set(v_a_2703_, v___x_2804_);
if (v_isShared_2778_ == 0)
{
v___x_2807_ = v___x_2777_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2775_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_2774_;
}
}
}
}
case 6:
{
if (v_a_2701_ == 0)
{
lean_object* v___x_2814_; lean_object* v_canon_2815_; lean_object* v_cache_2816_; lean_object* v___x_2817_; 
v___x_2814_ = lean_st_ref_get(v_a_2703_);
v_canon_2815_ = lean_ctor_get(v___x_2814_, 9);
lean_inc_ref(v_canon_2815_);
lean_dec(v___x_2814_);
v_cache_2816_ = lean_ctor_get(v_canon_2815_, 0);
lean_inc_ref(v_cache_2816_);
lean_dec_ref(v_canon_2815_);
v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2816_, v_e_2700_);
lean_dec_ref(v_cache_2816_);
if (lean_obj_tag(v___x_2817_) == 1)
{
lean_object* v_val_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_val_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set_tag(v___x_2820_, 0);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_val_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
lean_object* v___x_2826_; 
lean_dec(v___x_2817_);
lean_inc_ref(v_e_2700_);
v___x_2826_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2865_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2865_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2865_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v_canon_2832_; lean_object* v_share_2833_; lean_object* v_maxFVar_2834_; lean_object* v_proofInstInfo_2835_; lean_object* v_inferType_2836_; lean_object* v_getLevel_2837_; lean_object* v_congrInfo_2838_; lean_object* v_defEqI_2839_; lean_object* v_extensions_2840_; lean_object* v_issues_2841_; lean_object* v_instanceOverrides_2842_; uint8_t v_debug_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2864_; 
v___x_2831_ = lean_st_ref_take(v_a_2703_);
v_canon_2832_ = lean_ctor_get(v___x_2831_, 9);
v_share_2833_ = lean_ctor_get(v___x_2831_, 0);
v_maxFVar_2834_ = lean_ctor_get(v___x_2831_, 1);
v_proofInstInfo_2835_ = lean_ctor_get(v___x_2831_, 2);
v_inferType_2836_ = lean_ctor_get(v___x_2831_, 3);
v_getLevel_2837_ = lean_ctor_get(v___x_2831_, 4);
v_congrInfo_2838_ = lean_ctor_get(v___x_2831_, 5);
v_defEqI_2839_ = lean_ctor_get(v___x_2831_, 6);
v_extensions_2840_ = lean_ctor_get(v___x_2831_, 7);
v_issues_2841_ = lean_ctor_get(v___x_2831_, 8);
v_instanceOverrides_2842_ = lean_ctor_get(v___x_2831_, 10);
v_debug_2843_ = lean_ctor_get_uint8(v___x_2831_, sizeof(void*)*11);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2845_ = v___x_2831_;
v_isShared_2846_ = v_isSharedCheck_2864_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_instanceOverrides_2842_);
lean_inc(v_canon_2832_);
lean_inc(v_issues_2841_);
lean_inc(v_extensions_2840_);
lean_inc(v_defEqI_2839_);
lean_inc(v_congrInfo_2838_);
lean_inc(v_getLevel_2837_);
lean_inc(v_inferType_2836_);
lean_inc(v_proofInstInfo_2835_);
lean_inc(v_maxFVar_2834_);
lean_inc(v_share_2833_);
lean_dec(v___x_2831_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2864_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_cache_2847_; lean_object* v_cacheInType_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2863_; 
v_cache_2847_ = lean_ctor_get(v_canon_2832_, 0);
v_cacheInType_2848_ = lean_ctor_get(v_canon_2832_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_canon_2832_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2850_ = v_canon_2832_;
v_isShared_2851_ = v_isSharedCheck_2863_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_cacheInType_2848_);
lean_inc(v_cache_2847_);
lean_dec(v_canon_2832_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2863_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_inc(v_a_2827_);
v___x_2852_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2847_, v_e_2700_, v_a_2827_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_cacheInType_2848_);
v___x_2854_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 9, v___x_2854_);
v___x_2856_ = v___x_2845_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_share_2833_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_maxFVar_2834_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_proofInstInfo_2835_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_inferType_2836_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_getLevel_2837_);
lean_ctor_set(v_reuseFailAlloc_2861_, 5, v_congrInfo_2838_);
lean_ctor_set(v_reuseFailAlloc_2861_, 6, v_defEqI_2839_);
lean_ctor_set(v_reuseFailAlloc_2861_, 7, v_extensions_2840_);
lean_ctor_set(v_reuseFailAlloc_2861_, 8, v_issues_2841_);
lean_ctor_set(v_reuseFailAlloc_2861_, 9, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2861_, 10, v_instanceOverrides_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2861_, sizeof(void*)*11, v_debug_2843_);
v___x_2856_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_st_ref_set(v_a_2703_, v___x_2856_);
if (v_isShared_2830_ == 0)
{
v___x_2859_ = v___x_2829_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2827_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_2826_;
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v_canon_2867_; lean_object* v_cacheInType_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_st_ref_get(v_a_2703_);
v_canon_2867_ = lean_ctor_get(v___x_2866_, 9);
lean_inc_ref(v_canon_2867_);
lean_dec(v___x_2866_);
v_cacheInType_2868_ = lean_ctor_get(v_canon_2867_, 1);
lean_inc_ref(v_cacheInType_2868_);
lean_dec_ref(v_canon_2867_);
v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2868_, v_e_2700_);
lean_dec_ref(v_cacheInType_2868_);
if (lean_obj_tag(v___x_2869_) == 1)
{
lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 0);
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_val_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
else
{
lean_object* v___x_2878_; 
lean_dec(v___x_2869_);
lean_inc_ref(v_e_2700_);
v___x_2878_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2917_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2917_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2917_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v_canon_2884_; lean_object* v_share_2885_; lean_object* v_maxFVar_2886_; lean_object* v_proofInstInfo_2887_; lean_object* v_inferType_2888_; lean_object* v_getLevel_2889_; lean_object* v_congrInfo_2890_; lean_object* v_defEqI_2891_; lean_object* v_extensions_2892_; lean_object* v_issues_2893_; lean_object* v_instanceOverrides_2894_; uint8_t v_debug_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2916_; 
v___x_2883_ = lean_st_ref_take(v_a_2703_);
v_canon_2884_ = lean_ctor_get(v___x_2883_, 9);
v_share_2885_ = lean_ctor_get(v___x_2883_, 0);
v_maxFVar_2886_ = lean_ctor_get(v___x_2883_, 1);
v_proofInstInfo_2887_ = lean_ctor_get(v___x_2883_, 2);
v_inferType_2888_ = lean_ctor_get(v___x_2883_, 3);
v_getLevel_2889_ = lean_ctor_get(v___x_2883_, 4);
v_congrInfo_2890_ = lean_ctor_get(v___x_2883_, 5);
v_defEqI_2891_ = lean_ctor_get(v___x_2883_, 6);
v_extensions_2892_ = lean_ctor_get(v___x_2883_, 7);
v_issues_2893_ = lean_ctor_get(v___x_2883_, 8);
v_instanceOverrides_2894_ = lean_ctor_get(v___x_2883_, 10);
v_debug_2895_ = lean_ctor_get_uint8(v___x_2883_, sizeof(void*)*11);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2897_ = v___x_2883_;
v_isShared_2898_ = v_isSharedCheck_2916_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_instanceOverrides_2894_);
lean_inc(v_canon_2884_);
lean_inc(v_issues_2893_);
lean_inc(v_extensions_2892_);
lean_inc(v_defEqI_2891_);
lean_inc(v_congrInfo_2890_);
lean_inc(v_getLevel_2889_);
lean_inc(v_inferType_2888_);
lean_inc(v_proofInstInfo_2887_);
lean_inc(v_maxFVar_2886_);
lean_inc(v_share_2885_);
lean_dec(v___x_2883_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2916_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_cache_2899_; lean_object* v_cacheInType_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2915_; 
v_cache_2899_ = lean_ctor_get(v_canon_2884_, 0);
v_cacheInType_2900_ = lean_ctor_get(v_canon_2884_, 1);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_canon_2884_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2902_ = v_canon_2884_;
v_isShared_2903_ = v_isSharedCheck_2915_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_cacheInType_2900_);
lean_inc(v_cache_2899_);
lean_dec(v_canon_2884_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2915_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_inc(v_a_2879_);
v___x_2904_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2900_, v_e_2700_, v_a_2879_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 1, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_cache_2899_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 9, v___x_2906_);
v___x_2908_ = v___x_2897_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_share_2885_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_maxFVar_2886_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_proofInstInfo_2887_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_inferType_2888_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_getLevel_2889_);
lean_ctor_set(v_reuseFailAlloc_2913_, 5, v_congrInfo_2890_);
lean_ctor_set(v_reuseFailAlloc_2913_, 6, v_defEqI_2891_);
lean_ctor_set(v_reuseFailAlloc_2913_, 7, v_extensions_2892_);
lean_ctor_set(v_reuseFailAlloc_2913_, 8, v_issues_2893_);
lean_ctor_set(v_reuseFailAlloc_2913_, 9, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2913_, 10, v_instanceOverrides_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2913_, sizeof(void*)*11, v_debug_2895_);
v___x_2908_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2909_ = lean_st_ref_set(v_a_2703_, v___x_2908_);
if (v_isShared_2882_ == 0)
{
v___x_2911_ = v___x_2881_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2879_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_2878_;
}
}
}
}
case 8:
{
lean_object* v___x_2918_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2701_ == 0)
{
lean_object* v___x_2919_; lean_object* v_canon_2920_; lean_object* v_cache_2921_; lean_object* v___x_2922_; 
v___x_2919_ = lean_st_ref_get(v_a_2703_);
v_canon_2920_ = lean_ctor_get(v___x_2919_, 9);
lean_inc_ref(v_canon_2920_);
lean_dec(v___x_2919_);
v_cache_2921_ = lean_ctor_get(v_canon_2920_, 0);
lean_inc_ref(v_cache_2921_);
lean_dec_ref(v_canon_2920_);
v___x_2922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2921_, v_e_2700_);
lean_dec_ref(v_cache_2921_);
if (lean_obj_tag(v___x_2922_) == 1)
{
lean_object* v_val_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref_known(v_e_2700_, 4);
v_val_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_val_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set_tag(v___x_2925_, 0);
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_val_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_object* v___x_2931_; 
lean_dec(v___x_2922_);
lean_inc_ref(v_e_2700_);
v___x_2931_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2918_, v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2970_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2970_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2970_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v_canon_2937_; lean_object* v_share_2938_; lean_object* v_maxFVar_2939_; lean_object* v_proofInstInfo_2940_; lean_object* v_inferType_2941_; lean_object* v_getLevel_2942_; lean_object* v_congrInfo_2943_; lean_object* v_defEqI_2944_; lean_object* v_extensions_2945_; lean_object* v_issues_2946_; lean_object* v_instanceOverrides_2947_; uint8_t v_debug_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2969_; 
v___x_2936_ = lean_st_ref_take(v_a_2703_);
v_canon_2937_ = lean_ctor_get(v___x_2936_, 9);
v_share_2938_ = lean_ctor_get(v___x_2936_, 0);
v_maxFVar_2939_ = lean_ctor_get(v___x_2936_, 1);
v_proofInstInfo_2940_ = lean_ctor_get(v___x_2936_, 2);
v_inferType_2941_ = lean_ctor_get(v___x_2936_, 3);
v_getLevel_2942_ = lean_ctor_get(v___x_2936_, 4);
v_congrInfo_2943_ = lean_ctor_get(v___x_2936_, 5);
v_defEqI_2944_ = lean_ctor_get(v___x_2936_, 6);
v_extensions_2945_ = lean_ctor_get(v___x_2936_, 7);
v_issues_2946_ = lean_ctor_get(v___x_2936_, 8);
v_instanceOverrides_2947_ = lean_ctor_get(v___x_2936_, 10);
v_debug_2948_ = lean_ctor_get_uint8(v___x_2936_, sizeof(void*)*11);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2950_ = v___x_2936_;
v_isShared_2951_ = v_isSharedCheck_2969_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_instanceOverrides_2947_);
lean_inc(v_canon_2937_);
lean_inc(v_issues_2946_);
lean_inc(v_extensions_2945_);
lean_inc(v_defEqI_2944_);
lean_inc(v_congrInfo_2943_);
lean_inc(v_getLevel_2942_);
lean_inc(v_inferType_2941_);
lean_inc(v_proofInstInfo_2940_);
lean_inc(v_maxFVar_2939_);
lean_inc(v_share_2938_);
lean_dec(v___x_2936_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2969_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_cache_2952_; lean_object* v_cacheInType_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2968_; 
v_cache_2952_ = lean_ctor_get(v_canon_2937_, 0);
v_cacheInType_2953_ = lean_ctor_get(v_canon_2937_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_canon_2937_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2955_ = v_canon_2937_;
v_isShared_2956_ = v_isSharedCheck_2968_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_cacheInType_2953_);
lean_inc(v_cache_2952_);
lean_dec(v_canon_2937_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2968_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_inc(v_a_2932_);
v___x_2957_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2952_, v_e_2700_, v_a_2932_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_cacheInType_2953_);
v___x_2959_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 9, v___x_2959_);
v___x_2961_ = v___x_2950_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_share_2938_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_maxFVar_2939_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_proofInstInfo_2940_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_inferType_2941_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_getLevel_2942_);
lean_ctor_set(v_reuseFailAlloc_2966_, 5, v_congrInfo_2943_);
lean_ctor_set(v_reuseFailAlloc_2966_, 6, v_defEqI_2944_);
lean_ctor_set(v_reuseFailAlloc_2966_, 7, v_extensions_2945_);
lean_ctor_set(v_reuseFailAlloc_2966_, 8, v_issues_2946_);
lean_ctor_set(v_reuseFailAlloc_2966_, 9, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2966_, 10, v_instanceOverrides_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, sizeof(void*)*11, v_debug_2948_);
v___x_2961_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = lean_st_ref_set(v_a_2703_, v___x_2961_);
if (v_isShared_2935_ == 0)
{
v___x_2964_ = v___x_2934_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2932_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 4);
return v___x_2931_;
}
}
}
else
{
lean_object* v___x_2971_; lean_object* v_canon_2972_; lean_object* v_cacheInType_2973_; lean_object* v___x_2974_; 
v___x_2971_ = lean_st_ref_get(v_a_2703_);
v_canon_2972_ = lean_ctor_get(v___x_2971_, 9);
lean_inc_ref(v_canon_2972_);
lean_dec(v___x_2971_);
v_cacheInType_2973_ = lean_ctor_get(v_canon_2972_, 1);
lean_inc_ref(v_cacheInType_2973_);
lean_dec_ref(v_canon_2972_);
v___x_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2973_, v_e_2700_);
lean_dec_ref(v_cacheInType_2973_);
if (lean_obj_tag(v___x_2974_) == 1)
{
lean_object* v_val_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref_known(v_e_2700_, 4);
v_val_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_val_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 0);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_val_2975_);
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
lean_object* v___x_2983_; 
lean_dec(v___x_2974_);
lean_inc_ref(v_e_2700_);
v___x_2983_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2918_, v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3022_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3022_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3022_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v_canon_2989_; lean_object* v_share_2990_; lean_object* v_maxFVar_2991_; lean_object* v_proofInstInfo_2992_; lean_object* v_inferType_2993_; lean_object* v_getLevel_2994_; lean_object* v_congrInfo_2995_; lean_object* v_defEqI_2996_; lean_object* v_extensions_2997_; lean_object* v_issues_2998_; lean_object* v_instanceOverrides_2999_; uint8_t v_debug_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3021_; 
v___x_2988_ = lean_st_ref_take(v_a_2703_);
v_canon_2989_ = lean_ctor_get(v___x_2988_, 9);
v_share_2990_ = lean_ctor_get(v___x_2988_, 0);
v_maxFVar_2991_ = lean_ctor_get(v___x_2988_, 1);
v_proofInstInfo_2992_ = lean_ctor_get(v___x_2988_, 2);
v_inferType_2993_ = lean_ctor_get(v___x_2988_, 3);
v_getLevel_2994_ = lean_ctor_get(v___x_2988_, 4);
v_congrInfo_2995_ = lean_ctor_get(v___x_2988_, 5);
v_defEqI_2996_ = lean_ctor_get(v___x_2988_, 6);
v_extensions_2997_ = lean_ctor_get(v___x_2988_, 7);
v_issues_2998_ = lean_ctor_get(v___x_2988_, 8);
v_instanceOverrides_2999_ = lean_ctor_get(v___x_2988_, 10);
v_debug_3000_ = lean_ctor_get_uint8(v___x_2988_, sizeof(void*)*11);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3002_ = v___x_2988_;
v_isShared_3003_ = v_isSharedCheck_3021_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_instanceOverrides_2999_);
lean_inc(v_canon_2989_);
lean_inc(v_issues_2998_);
lean_inc(v_extensions_2997_);
lean_inc(v_defEqI_2996_);
lean_inc(v_congrInfo_2995_);
lean_inc(v_getLevel_2994_);
lean_inc(v_inferType_2993_);
lean_inc(v_proofInstInfo_2992_);
lean_inc(v_maxFVar_2991_);
lean_inc(v_share_2990_);
lean_dec(v___x_2988_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3021_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_cache_3004_; lean_object* v_cacheInType_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3020_; 
v_cache_3004_ = lean_ctor_get(v_canon_2989_, 0);
v_cacheInType_3005_ = lean_ctor_get(v_canon_2989_, 1);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_canon_2989_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3007_ = v_canon_2989_;
v_isShared_3008_ = v_isSharedCheck_3020_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_cacheInType_3005_);
lean_inc(v_cache_3004_);
lean_dec(v_canon_2989_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3020_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_inc(v_a_2984_);
v___x_3009_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3005_, v_e_2700_, v_a_2984_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_cache_3004_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 9, v___x_3011_);
v___x_3013_ = v___x_3002_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_share_2990_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_maxFVar_2991_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_proofInstInfo_2992_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_inferType_2993_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_getLevel_2994_);
lean_ctor_set(v_reuseFailAlloc_3018_, 5, v_congrInfo_2995_);
lean_ctor_set(v_reuseFailAlloc_3018_, 6, v_defEqI_2996_);
lean_ctor_set(v_reuseFailAlloc_3018_, 7, v_extensions_2997_);
lean_ctor_set(v_reuseFailAlloc_3018_, 8, v_issues_2998_);
lean_ctor_set(v_reuseFailAlloc_3018_, 9, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3018_, 10, v_instanceOverrides_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3018_, sizeof(void*)*11, v_debug_3000_);
v___x_3013_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3014_ = lean_st_ref_set(v_a_2703_, v___x_3013_);
if (v_isShared_2987_ == 0)
{
v___x_3016_ = v___x_2986_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_2984_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 4);
return v___x_2983_;
}
}
}
}
case 5:
{
if (v_a_2701_ == 0)
{
lean_object* v___x_3023_; lean_object* v_canon_3024_; lean_object* v_cache_3025_; lean_object* v___x_3026_; 
v___x_3023_ = lean_st_ref_get(v_a_2703_);
v_canon_3024_ = lean_ctor_get(v___x_3023_, 9);
lean_inc_ref(v_canon_3024_);
lean_dec(v___x_3023_);
v_cache_3025_ = lean_ctor_get(v_canon_3024_, 0);
lean_inc_ref(v_cache_3025_);
lean_dec_ref(v_canon_3024_);
v___x_3026_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3025_, v_e_2700_);
lean_dec_ref(v_cache_3025_);
if (lean_obj_tag(v___x_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref_known(v_e_2700_, 2);
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_val_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set_tag(v___x_3029_, 0);
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_val_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
else
{
lean_object* v___x_3035_; 
lean_dec(v___x_3026_);
lean_inc_ref(v_e_2700_);
v___x_3035_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3074_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3074_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3074_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v_canon_3041_; lean_object* v_share_3042_; lean_object* v_maxFVar_3043_; lean_object* v_proofInstInfo_3044_; lean_object* v_inferType_3045_; lean_object* v_getLevel_3046_; lean_object* v_congrInfo_3047_; lean_object* v_defEqI_3048_; lean_object* v_extensions_3049_; lean_object* v_issues_3050_; lean_object* v_instanceOverrides_3051_; uint8_t v_debug_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3073_; 
v___x_3040_ = lean_st_ref_take(v_a_2703_);
v_canon_3041_ = lean_ctor_get(v___x_3040_, 9);
v_share_3042_ = lean_ctor_get(v___x_3040_, 0);
v_maxFVar_3043_ = lean_ctor_get(v___x_3040_, 1);
v_proofInstInfo_3044_ = lean_ctor_get(v___x_3040_, 2);
v_inferType_3045_ = lean_ctor_get(v___x_3040_, 3);
v_getLevel_3046_ = lean_ctor_get(v___x_3040_, 4);
v_congrInfo_3047_ = lean_ctor_get(v___x_3040_, 5);
v_defEqI_3048_ = lean_ctor_get(v___x_3040_, 6);
v_extensions_3049_ = lean_ctor_get(v___x_3040_, 7);
v_issues_3050_ = lean_ctor_get(v___x_3040_, 8);
v_instanceOverrides_3051_ = lean_ctor_get(v___x_3040_, 10);
v_debug_3052_ = lean_ctor_get_uint8(v___x_3040_, sizeof(void*)*11);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3054_ = v___x_3040_;
v_isShared_3055_ = v_isSharedCheck_3073_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_instanceOverrides_3051_);
lean_inc(v_canon_3041_);
lean_inc(v_issues_3050_);
lean_inc(v_extensions_3049_);
lean_inc(v_defEqI_3048_);
lean_inc(v_congrInfo_3047_);
lean_inc(v_getLevel_3046_);
lean_inc(v_inferType_3045_);
lean_inc(v_proofInstInfo_3044_);
lean_inc(v_maxFVar_3043_);
lean_inc(v_share_3042_);
lean_dec(v___x_3040_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3073_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v_cache_3056_; lean_object* v_cacheInType_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3072_; 
v_cache_3056_ = lean_ctor_get(v_canon_3041_, 0);
v_cacheInType_3057_ = lean_ctor_get(v_canon_3041_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_canon_3041_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3059_ = v_canon_3041_;
v_isShared_3060_ = v_isSharedCheck_3072_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_cacheInType_3057_);
lean_inc(v_cache_3056_);
lean_dec(v_canon_3041_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3072_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_inc(v_a_3036_);
v___x_3061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3056_, v_e_2700_, v_a_3036_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_cacheInType_3057_);
v___x_3063_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3065_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 9, v___x_3063_);
v___x_3065_ = v___x_3054_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_share_3042_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_maxFVar_3043_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_proofInstInfo_3044_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_inferType_3045_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_getLevel_3046_);
lean_ctor_set(v_reuseFailAlloc_3070_, 5, v_congrInfo_3047_);
lean_ctor_set(v_reuseFailAlloc_3070_, 6, v_defEqI_3048_);
lean_ctor_set(v_reuseFailAlloc_3070_, 7, v_extensions_3049_);
lean_ctor_set(v_reuseFailAlloc_3070_, 8, v_issues_3050_);
lean_ctor_set(v_reuseFailAlloc_3070_, 9, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3070_, 10, v_instanceOverrides_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3070_, sizeof(void*)*11, v_debug_3052_);
v___x_3065_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_st_ref_set(v_a_2703_, v___x_3065_);
if (v_isShared_3039_ == 0)
{
v___x_3068_ = v___x_3038_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3036_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 2);
return v___x_3035_;
}
}
}
else
{
lean_object* v___x_3075_; lean_object* v_canon_3076_; lean_object* v_cacheInType_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_st_ref_get(v_a_2703_);
v_canon_3076_ = lean_ctor_get(v___x_3075_, 9);
lean_inc_ref(v_canon_3076_);
lean_dec(v___x_3075_);
v_cacheInType_3077_ = lean_ctor_get(v_canon_3076_, 1);
lean_inc_ref(v_cacheInType_3077_);
lean_dec_ref(v_canon_3076_);
v___x_3078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3077_, v_e_2700_);
lean_dec_ref(v_cacheInType_3077_);
if (lean_obj_tag(v___x_3078_) == 1)
{
lean_object* v_val_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref_known(v_e_2700_, 2);
v_val_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_val_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 0);
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_val_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
else
{
lean_object* v___x_3087_; 
lean_dec(v___x_3078_);
lean_inc_ref(v_e_2700_);
v___x_3087_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3126_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3126_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3126_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v_canon_3093_; lean_object* v_share_3094_; lean_object* v_maxFVar_3095_; lean_object* v_proofInstInfo_3096_; lean_object* v_inferType_3097_; lean_object* v_getLevel_3098_; lean_object* v_congrInfo_3099_; lean_object* v_defEqI_3100_; lean_object* v_extensions_3101_; lean_object* v_issues_3102_; lean_object* v_instanceOverrides_3103_; uint8_t v_debug_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3125_; 
v___x_3092_ = lean_st_ref_take(v_a_2703_);
v_canon_3093_ = lean_ctor_get(v___x_3092_, 9);
v_share_3094_ = lean_ctor_get(v___x_3092_, 0);
v_maxFVar_3095_ = lean_ctor_get(v___x_3092_, 1);
v_proofInstInfo_3096_ = lean_ctor_get(v___x_3092_, 2);
v_inferType_3097_ = lean_ctor_get(v___x_3092_, 3);
v_getLevel_3098_ = lean_ctor_get(v___x_3092_, 4);
v_congrInfo_3099_ = lean_ctor_get(v___x_3092_, 5);
v_defEqI_3100_ = lean_ctor_get(v___x_3092_, 6);
v_extensions_3101_ = lean_ctor_get(v___x_3092_, 7);
v_issues_3102_ = lean_ctor_get(v___x_3092_, 8);
v_instanceOverrides_3103_ = lean_ctor_get(v___x_3092_, 10);
v_debug_3104_ = lean_ctor_get_uint8(v___x_3092_, sizeof(void*)*11);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3106_ = v___x_3092_;
v_isShared_3107_ = v_isSharedCheck_3125_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_instanceOverrides_3103_);
lean_inc(v_canon_3093_);
lean_inc(v_issues_3102_);
lean_inc(v_extensions_3101_);
lean_inc(v_defEqI_3100_);
lean_inc(v_congrInfo_3099_);
lean_inc(v_getLevel_3098_);
lean_inc(v_inferType_3097_);
lean_inc(v_proofInstInfo_3096_);
lean_inc(v_maxFVar_3095_);
lean_inc(v_share_3094_);
lean_dec(v___x_3092_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3125_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_cache_3108_; lean_object* v_cacheInType_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3124_; 
v_cache_3108_ = lean_ctor_get(v_canon_3093_, 0);
v_cacheInType_3109_ = lean_ctor_get(v_canon_3093_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_canon_3093_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3111_ = v_canon_3093_;
v_isShared_3112_ = v_isSharedCheck_3124_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_cacheInType_3109_);
lean_inc(v_cache_3108_);
lean_dec(v_canon_3093_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3124_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_inc(v_a_3088_);
v___x_3113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3109_, v_e_2700_, v_a_3088_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3113_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_cache_3108_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 9, v___x_3115_);
v___x_3117_ = v___x_3106_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_share_3094_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_maxFVar_3095_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_proofInstInfo_3096_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_inferType_3097_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_getLevel_3098_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_congrInfo_3099_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_defEqI_3100_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v_extensions_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v_issues_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 9, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3122_, 10, v_instanceOverrides_3103_);
lean_ctor_set_uint8(v_reuseFailAlloc_3122_, sizeof(void*)*11, v_debug_3104_);
v___x_3117_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_st_ref_set(v_a_2703_, v___x_3117_);
if (v_isShared_3091_ == 0)
{
v___x_3120_ = v___x_3090_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3088_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 2);
return v___x_3087_;
}
}
}
}
case 11:
{
if (v_a_2701_ == 0)
{
lean_object* v___x_3127_; lean_object* v_canon_3128_; lean_object* v_cache_3129_; lean_object* v___x_3130_; 
v___x_3127_ = lean_st_ref_get(v_a_2703_);
v_canon_3128_ = lean_ctor_get(v___x_3127_, 9);
lean_inc_ref(v_canon_3128_);
lean_dec(v___x_3127_);
v_cache_3129_ = lean_ctor_get(v_canon_3128_, 0);
lean_inc_ref(v_cache_3129_);
lean_dec_ref(v_canon_3128_);
v___x_3130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3129_, v_e_2700_);
lean_dec_ref(v_cache_3129_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_val_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 0);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_val_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_object* v___x_3139_; 
lean_dec(v___x_3130_);
lean_inc_ref(v_e_2700_);
v___x_3139_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3178_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3178_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3178_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v_canon_3145_; lean_object* v_share_3146_; lean_object* v_maxFVar_3147_; lean_object* v_proofInstInfo_3148_; lean_object* v_inferType_3149_; lean_object* v_getLevel_3150_; lean_object* v_congrInfo_3151_; lean_object* v_defEqI_3152_; lean_object* v_extensions_3153_; lean_object* v_issues_3154_; lean_object* v_instanceOverrides_3155_; uint8_t v_debug_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3177_; 
v___x_3144_ = lean_st_ref_take(v_a_2703_);
v_canon_3145_ = lean_ctor_get(v___x_3144_, 9);
v_share_3146_ = lean_ctor_get(v___x_3144_, 0);
v_maxFVar_3147_ = lean_ctor_get(v___x_3144_, 1);
v_proofInstInfo_3148_ = lean_ctor_get(v___x_3144_, 2);
v_inferType_3149_ = lean_ctor_get(v___x_3144_, 3);
v_getLevel_3150_ = lean_ctor_get(v___x_3144_, 4);
v_congrInfo_3151_ = lean_ctor_get(v___x_3144_, 5);
v_defEqI_3152_ = lean_ctor_get(v___x_3144_, 6);
v_extensions_3153_ = lean_ctor_get(v___x_3144_, 7);
v_issues_3154_ = lean_ctor_get(v___x_3144_, 8);
v_instanceOverrides_3155_ = lean_ctor_get(v___x_3144_, 10);
v_debug_3156_ = lean_ctor_get_uint8(v___x_3144_, sizeof(void*)*11);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3158_ = v___x_3144_;
v_isShared_3159_ = v_isSharedCheck_3177_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_instanceOverrides_3155_);
lean_inc(v_canon_3145_);
lean_inc(v_issues_3154_);
lean_inc(v_extensions_3153_);
lean_inc(v_defEqI_3152_);
lean_inc(v_congrInfo_3151_);
lean_inc(v_getLevel_3150_);
lean_inc(v_inferType_3149_);
lean_inc(v_proofInstInfo_3148_);
lean_inc(v_maxFVar_3147_);
lean_inc(v_share_3146_);
lean_dec(v___x_3144_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3177_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_cache_3160_; lean_object* v_cacheInType_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3176_; 
v_cache_3160_ = lean_ctor_get(v_canon_3145_, 0);
v_cacheInType_3161_ = lean_ctor_get(v_canon_3145_, 1);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_canon_3145_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3163_ = v_canon_3145_;
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_cacheInType_3161_);
lean_inc(v_cache_3160_);
lean_dec(v_canon_3145_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
lean_inc(v_a_3140_);
v___x_3165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3160_, v_e_2700_, v_a_3140_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_cacheInType_3161_);
v___x_3167_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 9, v___x_3167_);
v___x_3169_ = v___x_3158_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_share_3146_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_maxFVar_3147_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_proofInstInfo_3148_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_inferType_3149_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_getLevel_3150_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v_congrInfo_3151_);
lean_ctor_set(v_reuseFailAlloc_3174_, 6, v_defEqI_3152_);
lean_ctor_set(v_reuseFailAlloc_3174_, 7, v_extensions_3153_);
lean_ctor_set(v_reuseFailAlloc_3174_, 8, v_issues_3154_);
lean_ctor_set(v_reuseFailAlloc_3174_, 9, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3174_, 10, v_instanceOverrides_3155_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*11, v_debug_3156_);
v___x_3169_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_st_ref_set(v_a_2703_, v___x_3169_);
if (v_isShared_3143_ == 0)
{
v___x_3172_ = v___x_3142_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3140_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_3139_;
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v_canon_3180_; lean_object* v_cacheInType_3181_; lean_object* v___x_3182_; 
v___x_3179_ = lean_st_ref_get(v_a_2703_);
v_canon_3180_ = lean_ctor_get(v___x_3179_, 9);
lean_inc_ref(v_canon_3180_);
lean_dec(v___x_3179_);
v_cacheInType_3181_ = lean_ctor_get(v_canon_3180_, 1);
lean_inc_ref(v_cacheInType_3181_);
lean_dec_ref(v_canon_3180_);
v___x_3182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3181_, v_e_2700_);
lean_dec_ref(v_cacheInType_3181_);
if (lean_obj_tag(v___x_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref_known(v_e_2700_, 3);
v_val_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_val_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_val_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
else
{
lean_object* v___x_3191_; 
lean_dec(v___x_3182_);
lean_inc_ref(v_e_2700_);
v___x_3191_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3230_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3230_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3230_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v_canon_3197_; lean_object* v_share_3198_; lean_object* v_maxFVar_3199_; lean_object* v_proofInstInfo_3200_; lean_object* v_inferType_3201_; lean_object* v_getLevel_3202_; lean_object* v_congrInfo_3203_; lean_object* v_defEqI_3204_; lean_object* v_extensions_3205_; lean_object* v_issues_3206_; lean_object* v_instanceOverrides_3207_; uint8_t v_debug_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3229_; 
v___x_3196_ = lean_st_ref_take(v_a_2703_);
v_canon_3197_ = lean_ctor_get(v___x_3196_, 9);
v_share_3198_ = lean_ctor_get(v___x_3196_, 0);
v_maxFVar_3199_ = lean_ctor_get(v___x_3196_, 1);
v_proofInstInfo_3200_ = lean_ctor_get(v___x_3196_, 2);
v_inferType_3201_ = lean_ctor_get(v___x_3196_, 3);
v_getLevel_3202_ = lean_ctor_get(v___x_3196_, 4);
v_congrInfo_3203_ = lean_ctor_get(v___x_3196_, 5);
v_defEqI_3204_ = lean_ctor_get(v___x_3196_, 6);
v_extensions_3205_ = lean_ctor_get(v___x_3196_, 7);
v_issues_3206_ = lean_ctor_get(v___x_3196_, 8);
v_instanceOverrides_3207_ = lean_ctor_get(v___x_3196_, 10);
v_debug_3208_ = lean_ctor_get_uint8(v___x_3196_, sizeof(void*)*11);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3210_ = v___x_3196_;
v_isShared_3211_ = v_isSharedCheck_3229_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_instanceOverrides_3207_);
lean_inc(v_canon_3197_);
lean_inc(v_issues_3206_);
lean_inc(v_extensions_3205_);
lean_inc(v_defEqI_3204_);
lean_inc(v_congrInfo_3203_);
lean_inc(v_getLevel_3202_);
lean_inc(v_inferType_3201_);
lean_inc(v_proofInstInfo_3200_);
lean_inc(v_maxFVar_3199_);
lean_inc(v_share_3198_);
lean_dec(v___x_3196_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3229_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_cache_3212_; lean_object* v_cacheInType_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3228_; 
v_cache_3212_ = lean_ctor_get(v_canon_3197_, 0);
v_cacheInType_3213_ = lean_ctor_get(v_canon_3197_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_canon_3197_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3215_ = v_canon_3197_;
v_isShared_3216_ = v_isSharedCheck_3228_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_cacheInType_3213_);
lean_inc(v_cache_3212_);
lean_dec(v_canon_3197_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3228_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
lean_inc(v_a_3192_);
v___x_3217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3213_, v_e_2700_, v_a_3192_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v___x_3217_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_cache_3212_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3221_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 9, v___x_3219_);
v___x_3221_ = v___x_3210_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_share_3198_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_maxFVar_3199_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_proofInstInfo_3200_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_inferType_3201_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_getLevel_3202_);
lean_ctor_set(v_reuseFailAlloc_3226_, 5, v_congrInfo_3203_);
lean_ctor_set(v_reuseFailAlloc_3226_, 6, v_defEqI_3204_);
lean_ctor_set(v_reuseFailAlloc_3226_, 7, v_extensions_3205_);
lean_ctor_set(v_reuseFailAlloc_3226_, 8, v_issues_3206_);
lean_ctor_set(v_reuseFailAlloc_3226_, 9, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3226_, 10, v_instanceOverrides_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3226_, sizeof(void*)*11, v_debug_3208_);
v___x_3221_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_st_ref_set(v_a_2703_, v___x_3221_);
if (v_isShared_3195_ == 0)
{
v___x_3224_ = v___x_3194_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3192_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 3);
return v___x_3191_;
}
}
}
}
case 10:
{
lean_object* v_data_3231_; lean_object* v_expr_3232_; lean_object* v___x_3233_; 
v_data_3231_ = lean_ctor_get(v_e_2700_, 0);
v_expr_3232_ = lean_ctor_get(v_e_2700_, 1);
lean_inc_ref(v_expr_3232_);
v___x_3233_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3232_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3248_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3248_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3248_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
size_t v___x_3238_; size_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3238_ = lean_ptr_addr(v_expr_3232_);
v___x_3239_ = lean_ptr_addr(v_a_3234_);
v___x_3240_ = lean_usize_dec_eq(v___x_3238_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_inc(v_data_3231_);
lean_dec_ref_known(v_e_2700_, 2);
v___x_3241_ = l_Lean_Expr_mdata___override(v_data_3231_, v_a_3234_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3241_);
v___x_3243_ = v___x_3236_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
else
{
lean_object* v___x_3246_; 
lean_dec(v_a_3234_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_e_2700_);
v___x_3246_ = v___x_3236_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_e_2700_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2700_, 2);
return v___x_3233_;
}
}
default: 
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_e_2700_);
return v___x_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3250_, uint8_t v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
if (v_a_3251_ == 0)
{
lean_object* v___x_3259_; 
lean_inc_ref(v_e_3250_);
v___x_3259_ = l_Lean_Meta_isProp(v_e_3250_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
if (v___x_3261_ == 0)
{
uint8_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = 1;
v___x_3263_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3250_, v___x_3262_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; 
v___x_3264_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3264_;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_e_3250_);
v_a_3265_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3259_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3259_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v___x_3273_; 
v___x_3273_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3274_, lean_object* v_body_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
uint8_t v___y_65265__boxed_3285_; lean_object* v_res_3286_; 
v___y_65265__boxed_3285_ = lean_unbox(v___y_3277_);
v_res_3286_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3274_, v_body_3275_, v_x_3276_, v___y_65265__boxed_3285_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3287_, lean_object* v_e_3288_, uint8_t v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
if (lean_obj_tag(v_e_3288_) == 7)
{
lean_object* v_binderName_3297_; lean_object* v_binderType_3298_; lean_object* v_body_3299_; uint8_t v_binderInfo_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_binderName_3297_ = lean_ctor_get(v_e_3288_, 0);
lean_inc(v_binderName_3297_);
v_binderType_3298_ = lean_ctor_get(v_e_3288_, 1);
lean_inc_ref(v_binderType_3298_);
v_body_3299_ = lean_ctor_get(v_e_3288_, 2);
lean_inc_ref(v_body_3299_);
v_binderInfo_3300_ = lean_ctor_get_uint8(v_e_3288_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3288_, 3);
v___x_3301_ = lean_expr_instantiate_rev(v_binderType_3298_, v_fvars_3287_);
lean_dec_ref(v_binderType_3298_);
v___x_3302_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3301_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___f_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___f_3304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3304_, 0, v_fvars_3287_);
lean_closure_set(v___f_3304_, 1, v_body_3299_);
v___x_3305_ = 0;
v___x_3306_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3297_, v_binderInfo_3300_, v_a_3303_, v___f_3304_, v___x_3305_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
return v___x_3306_;
}
else
{
lean_dec_ref(v_body_3299_);
lean_dec(v_binderName_3297_);
lean_dec_ref(v_fvars_3287_);
return v___x_3302_;
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_expr_instantiate_rev(v_e_3288_, v_fvars_3287_);
lean_dec_ref(v_e_3288_);
v___x_3308_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3307_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; uint8_t v___x_3310_; uint8_t v___x_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = 0;
v___x_3311_ = 1;
v___x_3312_ = 1;
v___x_3313_ = l_Lean_Meta_mkForallFVars(v_fvars_3287_, v_a_3309_, v___x_3310_, v___x_3311_, v___x_3311_, v___x_3312_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
lean_dec_ref(v_fvars_3287_);
return v___x_3313_;
}
else
{
lean_dec_ref(v_fvars_3287_);
return v___x_3308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3314_, lean_object* v_body_3315_, lean_object* v_x_3316_, uint8_t v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_array_push(v_fvars_3314_, v_x_3316_);
v___x_3326_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3325_, v_body_3315_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
uint8_t v_a_boxed_3336_; lean_object* v_res_3337_; 
v_a_boxed_3336_ = lean_unbox(v_a_3328_);
v_res_3337_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3327_, v_a_boxed_3336_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
uint8_t v_a_boxed_3347_; lean_object* v_res_3348_; 
v_a_boxed_3347_ = lean_unbox(v_a_3339_);
v_res_3348_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3338_, v_a_boxed_3347_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_a_boxed_3358_; lean_object* v_res_3359_; 
v_a_boxed_3358_ = lean_unbox(v_a_3350_);
v_res_3359_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3349_, v_a_boxed_3358_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3360_, lean_object* v_report_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
uint8_t v_report_boxed_3370_; uint8_t v_a_boxed_3371_; lean_object* v_res_3372_; 
v_report_boxed_3370_ = lean_unbox(v_report_3361_);
v_a_boxed_3371_ = lean_unbox(v_a_3362_);
v_res_3372_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3360_, v_report_boxed_3370_, v_a_boxed_3371_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
uint8_t v_a_boxed_3382_; lean_object* v_res_3383_; 
v_a_boxed_3382_ = lean_unbox(v_a_3374_);
v_res_3383_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3373_, v_a_boxed_3382_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
uint8_t v_a_boxed_3393_; lean_object* v_res_3394_; 
v_a_boxed_3393_ = lean_unbox(v_a_3385_);
v_res_3394_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3384_, v_a_boxed_3393_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3395_, lean_object* v_e_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
uint8_t v_a_boxed_3405_; lean_object* v_res_3406_; 
v_a_boxed_3405_ = lean_unbox(v_a_3397_);
v_res_3406_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3395_, v_e_3396_, v_a_boxed_3405_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3407_, lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
uint8_t v_a_boxed_3417_; lean_object* v_res_3418_; 
v_a_boxed_3417_ = lean_unbox(v_a_3409_);
v_res_3418_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3407_, v_e_3408_, v_a_boxed_3417_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
uint8_t v_a_boxed_3428_; lean_object* v_res_3429_; 
v_a_boxed_3428_ = lean_unbox(v_a_3420_);
v_res_3429_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3419_, v_a_boxed_3428_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3430_, lean_object* v_e_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
uint8_t v_a_boxed_3440_; lean_object* v_res_3441_; 
v_a_boxed_3440_ = lean_unbox(v_a_3432_);
v_res_3441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3430_, v_e_3431_, v_a_boxed_3440_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3442_, lean_object* v_00_u03b1_3443_, lean_object* v_c_3444_, lean_object* v_a_3445_, lean_object* v_b_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
uint8_t v_a_boxed_3455_; lean_object* v_res_3456_; 
v_a_boxed_3455_ = lean_unbox(v_a_3447_);
v_res_3456_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3442_, v_00_u03b1_3443_, v_c_3444_, v_a_3445_, v_b_3446_, v_a_boxed_3455_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3457_, lean_object* v_00_u03b1_3458_, lean_object* v_c_3459_, lean_object* v_inst_3460_, lean_object* v_a_3461_, lean_object* v_b_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
uint8_t v_a_boxed_3471_; lean_object* v_res_3472_; 
v_a_boxed_3471_ = lean_unbox(v_a_3463_);
v_res_3472_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3457_, v_00_u03b1_3458_, v_c_3459_, v_inst_3460_, v_a_3461_, v_b_3462_, v_a_boxed_3471_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
uint8_t v_a_boxed_3482_; lean_object* v_res_3483_; 
v_a_boxed_3482_ = lean_unbox(v_a_3474_);
v_res_3483_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3473_, v_a_boxed_3482_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
uint8_t v_a_boxed_3493_; lean_object* v_res_3494_; 
v_a_boxed_3493_ = lean_unbox(v_a_3485_);
v_res_3494_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3484_, v_a_boxed_3493_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3495_, lean_object* v_prop_3496_, lean_object* v_inst_3497_, lean_object* v_e_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
uint8_t v_a_boxed_3507_; lean_object* v_res_3508_; 
v_a_boxed_3507_ = lean_unbox(v_a_3499_);
v_res_3508_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3495_, v_prop_3496_, v_inst_3497_, v_e_3498_, v_a_boxed_3507_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3509_, lean_object* v_report_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
uint8_t v_report_boxed_3519_; uint8_t v_a_boxed_3520_; lean_object* v_res_3521_; 
v_report_boxed_3519_ = lean_unbox(v_report_3510_);
v_a_boxed_3520_ = lean_unbox(v_a_3511_);
v_res_3521_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3509_, v_report_boxed_3519_, v_a_boxed_3520_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3522_, lean_object* v_prop_3523_, lean_object* v_h_3524_, lean_object* v_e_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
uint8_t v_a_boxed_3534_; lean_object* v_res_3535_; 
v_a_boxed_3534_ = lean_unbox(v_a_3526_);
v_res_3535_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3522_, v_prop_3523_, v_h_3524_, v_e_3525_, v_a_boxed_3534_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
uint8_t v_a_boxed_3545_; lean_object* v_res_3546_; 
v_a_boxed_3545_ = lean_unbox(v_a_3537_);
v_res_3546_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3536_, v_a_boxed_3545_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3547_, lean_object* v___x_3548_, lean_object* v_a_3549_, lean_object* v_b_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
uint8_t v___y_65686__boxed_3559_; lean_object* v_res_3560_; 
v___y_65686__boxed_3559_ = lean_unbox(v___y_3551_);
v_res_3560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3547_, v___x_3548_, v_a_3549_, v_b_3550_, v___y_65686__boxed_3559_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec_ref(v___x_3548_);
lean_dec(v_upperBound_3547_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3561_, lean_object* v_a_3562_, lean_object* v___x_3563_, lean_object* v_snd_3564_, lean_object* v___x_3565_, lean_object* v_fst_3566_, lean_object* v_____r_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
uint8_t v___x_65751__boxed_3576_; uint8_t v___y_65753__boxed_3577_; lean_object* v_res_3578_; 
v___x_65751__boxed_3576_ = lean_unbox(v___x_3565_);
v___y_65753__boxed_3577_ = lean_unbox(v___y_3568_);
v_res_3578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3561_, v_a_3562_, v___x_3563_, v_snd_3564_, v___x_65751__boxed_3576_, v_fst_3566_, v_____r_3567_, v___y_65753__boxed_3577_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v_a_3562_);
lean_dec_ref(v___x_3561_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3579_, lean_object* v_prop_3580_, lean_object* v_h_3581_, lean_object* v_e_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
uint8_t v_a_boxed_3591_; lean_object* v_res_3592_; 
v_a_boxed_3591_ = lean_unbox(v_a_3583_);
v_res_3592_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3579_, v_prop_3580_, v_h_3581_, v_e_3582_, v_a_boxed_3591_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
uint8_t v___y_65877__boxed_3605_; lean_object* v_res_3606_; 
v___y_65877__boxed_3605_ = lean_unbox(v___y_3597_);
v_res_3606_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3593_, v_x_3594_, v_x_3595_, v_x_3596_, v___y_65877__boxed_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
uint8_t v_a_boxed_3616_; lean_object* v_res_3617_; 
v_a_boxed_3616_ = lean_unbox(v_a_3608_);
v_res_3617_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3607_, v_a_boxed_3616_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3618_, uint8_t v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3618_, v___y_3625_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v___y_68183__boxed_3637_; lean_object* v_res_3638_; 
v___y_68183__boxed_3637_ = lean_unbox(v___y_3629_);
v_res_3638_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3628_, v___y_68183__boxed_3637_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3639_, lean_object* v_name_3640_, lean_object* v_type_3641_, lean_object* v_val_3642_, lean_object* v_k_3643_, uint8_t v_nondep_3644_, uint8_t v_kind_3645_, uint8_t v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3640_, v_type_3641_, v_val_3642_, v_k_3643_, v_nondep_3644_, v_kind_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3655_, lean_object* v_name_3656_, lean_object* v_type_3657_, lean_object* v_val_3658_, lean_object* v_k_3659_, lean_object* v_nondep_3660_, lean_object* v_kind_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_nondep_boxed_3670_; uint8_t v_kind_boxed_3671_; uint8_t v___y_68209__boxed_3672_; lean_object* v_res_3673_; 
v_nondep_boxed_3670_ = lean_unbox(v_nondep_3660_);
v_kind_boxed_3671_ = lean_unbox(v_kind_3661_);
v___y_68209__boxed_3672_ = lean_unbox(v___y_3662_);
v_res_3673_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3655_, v_name_3656_, v_type_3657_, v_val_3658_, v_k_3659_, v_nondep_boxed_3670_, v_kind_boxed_3671_, v___y_68209__boxed_3672_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3674_, lean_object* v_name_3675_, uint8_t v_bi_3676_, lean_object* v_type_3677_, lean_object* v_k_3678_, uint8_t v_kind_3679_, uint8_t v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3675_, v_bi_3676_, v_type_3677_, v_k_3678_, v_kind_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3689_, lean_object* v_name_3690_, lean_object* v_bi_3691_, lean_object* v_type_3692_, lean_object* v_k_3693_, lean_object* v_kind_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_bi_boxed_3703_; uint8_t v_kind_boxed_3704_; uint8_t v___y_68235__boxed_3705_; lean_object* v_res_3706_; 
v_bi_boxed_3703_ = lean_unbox(v_bi_3691_);
v_kind_boxed_3704_ = lean_unbox(v_kind_3694_);
v___y_68235__boxed_3705_ = lean_unbox(v___y_3695_);
v_res_3706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3689_, v_name_3690_, v_bi_boxed_3703_, v_type_3692_, v_k_3693_, v_kind_boxed_3704_, v___y_68235__boxed_3705_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3707_, lean_object* v_m_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3708_, v_a_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3711_, lean_object* v_m_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3711_, v_m_3712_, v_a_3713_);
lean_dec_ref(v_a_3713_);
lean_dec_ref(v_m_3712_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3715_, lean_object* v_m_3716_, lean_object* v_a_3717_, lean_object* v_b_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3716_, v_a_3717_, v_b_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3720_, lean_object* v_msg_3721_, uint8_t v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3720_, v_msg_3721_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3731_, lean_object* v_msg_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v___y_68265__boxed_3741_; lean_object* v_res_3742_; 
v___y_68265__boxed_3741_ = lean_unbox(v___y_3733_);
v_res_3742_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3731_, v_msg_3732_, v___y_68265__boxed_3741_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3743_, lean_object* v___x_3744_, lean_object* v___x_3745_, lean_object* v_inst_3746_, lean_object* v_R_3747_, lean_object* v_a_3748_, lean_object* v_b_3749_, lean_object* v_c_3750_, uint8_t v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3743_, v___x_3745_, v_a_3748_, v_b_3749_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3760_, lean_object* v___x_3761_, lean_object* v___x_3762_, lean_object* v_inst_3763_, lean_object* v_R_3764_, lean_object* v_a_3765_, lean_object* v_b_3766_, lean_object* v_c_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
uint8_t v___y_68295__boxed_3776_; lean_object* v_res_3777_; 
v___y_68295__boxed_3776_ = lean_unbox(v___y_3768_);
v_res_3777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3760_, v___x_3761_, v___x_3762_, v_inst_3763_, v_R_3764_, v_a_3765_, v_b_3766_, v_c_3767_, v___y_68295__boxed_3776_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec(v_upperBound_3760_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3778_, lean_object* v_a_3779_, lean_object* v_x_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3779_, v_x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3782_, lean_object* v_a_3783_, lean_object* v_x_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3782_, v_a_3783_, v_x_3784_);
lean_dec(v_x_3784_);
lean_dec_ref(v_a_3783_);
return v_res_3785_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3786_, lean_object* v_a_3787_, lean_object* v_x_3788_){
_start:
{
uint8_t v___x_3789_; 
v___x_3789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3787_, v_x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3790_, lean_object* v_a_3791_, lean_object* v_x_3792_){
_start:
{
uint8_t v_res_3793_; lean_object* v_r_3794_; 
v_res_3793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3790_, v_a_3791_, v_x_3792_);
lean_dec(v_x_3792_);
lean_dec_ref(v_a_3791_);
v_r_3794_ = lean_box(v_res_3793_);
return v_r_3794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3795_, lean_object* v_data_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3798_, lean_object* v_a_3799_, lean_object* v_b_3800_, lean_object* v_x_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3799_, v_b_3800_, v_x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3803_, lean_object* v_i_3804_, lean_object* v_source_3805_, lean_object* v_target_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3804_, v_source_3805_, v_target_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3809_, v_x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3812_, lean_object* v_i_3813_, lean_object* v_arg_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3812_, v_i_3813_, v_arg_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3836_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3836_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3836_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_unbox(v_a_3821_);
lean_dec(v_a_3821_);
if (v___x_3825_ == 3)
{
uint8_t v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3826_ = 0;
v___x_3827_ = lean_box(v___x_3826_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3827_);
v___x_3829_ = v___x_3823_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
else
{
uint8_t v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3831_ = 1;
v___x_3832_ = lean_box(v___x_3831_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3832_);
v___x_3834_ = v___x_3823_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3820_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3820_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3845_, lean_object* v_i_3846_, lean_object* v_arg_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3845_, v_i_3846_, v_arg_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_i_3846_);
lean_dec_ref(v_pinfos_3845_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3854_, lean_object* v_opts_3855_, lean_object* v_act_3856_, lean_object* v_decl_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
v___x_3865_ = lean_apply_6(v_act_3856_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
v___x_3866_ = l_Lean_profileitIOUnsafe___redArg(v_category_3854_, v_opts_3855_, v___x_3865_, v_decl_3857_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3867_, lean_object* v_opts_3868_, lean_object* v_act_3869_, lean_object* v_decl_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3867_, v_opts_3868_, v_act_3869_, v_decl_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v_opts_3868_);
lean_dec_ref(v_category_3867_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3879_, lean_object* v_category_3880_, lean_object* v_opts_3881_, lean_object* v_act_3882_, lean_object* v_decl_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3880_, v_opts_3881_, v_act_3882_, v_decl_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3892_, lean_object* v_category_3893_, lean_object* v_opts_3894_, lean_object* v_act_3895_, lean_object* v_decl_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3892_, v_category_3893_, v_opts_3894_, v_act_3895_, v_decl_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_opts_3894_);
lean_dec_ref(v_category_3893_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3905_, lean_object* v_e_3906_, uint8_t v___x_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___x_3915_; uint8_t v_foApprox_3916_; uint8_t v_ctxApprox_3917_; uint8_t v_quasiPatternApprox_3918_; uint8_t v_constApprox_3919_; uint8_t v_isDefEqStuckEx_3920_; uint8_t v_unificationHints_3921_; uint8_t v_proofIrrelevance_3922_; uint8_t v_assignSyntheticOpaque_3923_; uint8_t v_offsetCnstrs_3924_; uint8_t v_etaStruct_3925_; uint8_t v_univApprox_3926_; uint8_t v_iota_3927_; uint8_t v_beta_3928_; uint8_t v_proj_3929_; uint8_t v_zeta_3930_; uint8_t v_zetaDelta_3931_; uint8_t v_zetaUnused_3932_; uint8_t v_zetaHave_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3959_; 
v___x_3915_ = l_Lean_Meta_Context_config(v___y_3910_);
v_foApprox_3916_ = lean_ctor_get_uint8(v___x_3915_, 0);
v_ctxApprox_3917_ = lean_ctor_get_uint8(v___x_3915_, 1);
v_quasiPatternApprox_3918_ = lean_ctor_get_uint8(v___x_3915_, 2);
v_constApprox_3919_ = lean_ctor_get_uint8(v___x_3915_, 3);
v_isDefEqStuckEx_3920_ = lean_ctor_get_uint8(v___x_3915_, 4);
v_unificationHints_3921_ = lean_ctor_get_uint8(v___x_3915_, 5);
v_proofIrrelevance_3922_ = lean_ctor_get_uint8(v___x_3915_, 6);
v_assignSyntheticOpaque_3923_ = lean_ctor_get_uint8(v___x_3915_, 7);
v_offsetCnstrs_3924_ = lean_ctor_get_uint8(v___x_3915_, 8);
v_etaStruct_3925_ = lean_ctor_get_uint8(v___x_3915_, 10);
v_univApprox_3926_ = lean_ctor_get_uint8(v___x_3915_, 11);
v_iota_3927_ = lean_ctor_get_uint8(v___x_3915_, 12);
v_beta_3928_ = lean_ctor_get_uint8(v___x_3915_, 13);
v_proj_3929_ = lean_ctor_get_uint8(v___x_3915_, 14);
v_zeta_3930_ = lean_ctor_get_uint8(v___x_3915_, 15);
v_zetaDelta_3931_ = lean_ctor_get_uint8(v___x_3915_, 16);
v_zetaUnused_3932_ = lean_ctor_get_uint8(v___x_3915_, 17);
v_zetaHave_3933_ = lean_ctor_get_uint8(v___x_3915_, 18);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3935_ = v___x_3915_;
v_isShared_3936_ = v_isSharedCheck_3959_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v___x_3915_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3959_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
uint8_t v_trackZetaDelta_3937_; lean_object* v_zetaDeltaSet_3938_; lean_object* v_lctx_3939_; lean_object* v_localInstances_3940_; lean_object* v_defEqCtx_x3f_3941_; lean_object* v_synthPendingDepth_3942_; lean_object* v_canUnfold_x3f_3943_; uint8_t v_univApprox_3944_; uint8_t v_inTypeClassResolution_3945_; uint8_t v_cacheInferType_3946_; lean_object* v_config_3948_; 
v_trackZetaDelta_3937_ = lean_ctor_get_uint8(v___y_3910_, sizeof(void*)*7);
v_zetaDeltaSet_3938_ = lean_ctor_get(v___y_3910_, 1);
v_lctx_3939_ = lean_ctor_get(v___y_3910_, 2);
v_localInstances_3940_ = lean_ctor_get(v___y_3910_, 3);
v_defEqCtx_x3f_3941_ = lean_ctor_get(v___y_3910_, 4);
v_synthPendingDepth_3942_ = lean_ctor_get(v___y_3910_, 5);
v_canUnfold_x3f_3943_ = lean_ctor_get(v___y_3910_, 6);
v_univApprox_3944_ = lean_ctor_get_uint8(v___y_3910_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3945_ = lean_ctor_get_uint8(v___y_3910_, sizeof(void*)*7 + 2);
v_cacheInferType_3946_ = lean_ctor_get_uint8(v___y_3910_, sizeof(void*)*7 + 3);
if (v_isShared_3936_ == 0)
{
v_config_3948_ = v___x_3935_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 0, v_foApprox_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 1, v_ctxApprox_3917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 2, v_quasiPatternApprox_3918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 3, v_constApprox_3919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 4, v_isDefEqStuckEx_3920_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 5, v_unificationHints_3921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 6, v_proofIrrelevance_3922_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 7, v_assignSyntheticOpaque_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 8, v_offsetCnstrs_3924_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 10, v_etaStruct_3925_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 11, v_univApprox_3926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 12, v_iota_3927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 13, v_beta_3928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 14, v_proj_3929_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 15, v_zeta_3930_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 16, v_zetaDelta_3931_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 17, v_zetaUnused_3932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, 18, v_zetaHave_3933_);
v_config_3948_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
uint64_t v___x_3949_; uint64_t v___x_3950_; uint64_t v___x_3951_; uint64_t v___x_3952_; uint64_t v___x_3953_; uint64_t v_key_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
lean_ctor_set_uint8(v_config_3948_, 9, v___x_3905_);
v___x_3949_ = l_Lean_Meta_Context_configKey(v___y_3910_);
v___x_3950_ = 3ULL;
v___x_3951_ = lean_uint64_shift_right(v___x_3949_, v___x_3950_);
v___x_3952_ = lean_uint64_shift_left(v___x_3951_, v___x_3950_);
v___x_3953_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3905_);
v_key_3954_ = lean_uint64_lor(v___x_3952_, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3955_, 0, v_config_3948_);
lean_ctor_set_uint64(v___x_3955_, sizeof(void*)*1, v_key_3954_);
lean_inc(v_canUnfold_x3f_3943_);
lean_inc(v_synthPendingDepth_3942_);
lean_inc(v_defEqCtx_x3f_3941_);
lean_inc_ref(v_localInstances_3940_);
lean_inc_ref(v_lctx_3939_);
lean_inc(v_zetaDeltaSet_3938_);
v___x_3956_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
lean_ctor_set(v___x_3956_, 1, v_zetaDeltaSet_3938_);
lean_ctor_set(v___x_3956_, 2, v_lctx_3939_);
lean_ctor_set(v___x_3956_, 3, v_localInstances_3940_);
lean_ctor_set(v___x_3956_, 4, v_defEqCtx_x3f_3941_);
lean_ctor_set(v___x_3956_, 5, v_synthPendingDepth_3942_);
lean_ctor_set(v___x_3956_, 6, v_canUnfold_x3f_3943_);
lean_ctor_set_uint8(v___x_3956_, sizeof(void*)*7, v_trackZetaDelta_3937_);
lean_ctor_set_uint8(v___x_3956_, sizeof(void*)*7 + 1, v_univApprox_3944_);
lean_ctor_set_uint8(v___x_3956_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3945_);
lean_ctor_set_uint8(v___x_3956_, sizeof(void*)*7 + 3, v_cacheInferType_3946_);
v___x_3957_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3906_, v___x_3907_, v___y_3908_, v___y_3909_, v___x_3956_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec_ref_known(v___x_3956_, 7);
return v___x_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3960_, lean_object* v_e_3961_, lean_object* v___x_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v___x_2440__boxed_3970_; uint8_t v___x_2441__boxed_3971_; lean_object* v_res_3972_; 
v___x_2440__boxed_3970_ = lean_unbox(v___x_3960_);
v___x_2441__boxed_3971_ = lean_unbox(v___x_3962_);
v_res_3972_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3970_, v_e_3961_, v___x_2441__boxed_3971_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_options_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; uint8_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_options_3982_ = lean_ctor_get(v_a_3979_, 2);
v___x_3983_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3984_ = 0;
v___x_3985_ = 2;
v___x_3986_ = lean_box(v___x_3985_);
v___x_3987_ = lean_box(v___x_3984_);
v___f_3988_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3988_, 0, v___x_3986_);
lean_closure_set(v___f_3988_, 1, v_e_3974_);
lean_closure_set(v___f_3988_, 2, v___x_3987_);
v___x_3989_ = lean_box(0);
v___x_3990_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3983_, v_options_3982_, v___f_3988_, v___x_3989_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_Meta_Sym_canon(v_e_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
return v_res_3999_;
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
